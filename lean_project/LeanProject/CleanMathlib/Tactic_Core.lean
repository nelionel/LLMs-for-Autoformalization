import Lean.Elab.PreDefinition.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Util.Paths
import Lean.Meta.Tactic.Intro
import Mathlib.Lean.Expr.Basic
import Batteries.Tactic.OpenPrivate
open Lean.Elab.Tactic
namespace Lean
open Elab Meta
def toModifiers (nm : Name) (newDoc : Option String := none) :
    CoreM Modifiers := do
  let env ← getEnv
  let d ← getConstInfo nm
  let mods : Modifiers :=
  { docString? := newDoc
    visibility :=
    if isPrivateNameExport nm then
      Visibility.private
    else if isProtected env nm then
      Visibility.regular
    else
      Visibility.protected
    isNoncomputable := if (env.find? <| nm.mkStr "_cstage1").isSome then false else true
    recKind := RecKind.default 
    isUnsafe := d.isUnsafe
    attrs := #[] }
  return mods
def toPreDefinition (nm newNm : Name) (newType newValue : Expr) (newDoc : Option String := none) :
    CoreM PreDefinition := do
  let d ← getConstInfo nm
  let mods ← toModifiers nm newDoc
  let predef : PreDefinition :=
  { ref := Syntax.missing
    kind := if d.isDef then DefKind.def else DefKind.theorem
    levelParams := d.levelParams
    modifiers := mods
    declName := newNm
    type := newType
    value := newValue
    termination := .none }
  return predef
def setProtected {m : Type → Type} [MonadEnv m] (nm : Name) : m Unit :=
  modifyEnv (addProtected · nm)
def MVarId.introsWithBinderIdents
    (g : MVarId) (ids : List (TSyntax ``binderIdent)) :
    MetaM (List (TSyntax ``binderIdent) × Array FVarId × MVarId) := do
  let type ← g.getType
  let type ← instantiateMVars type
  let n := getIntrosSize type
  if n == 0 then
    return (ids, #[], g)
  let mut ids := ids
  let mut names := #[]
  for _ in [0:n] do
    names := names.push (ids.headD (Unhygienic.run `(binderIdent| _)))
    ids := ids.tail
  let (xs, g) ← g.introN n <| names.toList.map fun stx =>
    match stx.raw with
    | `(binderIdent| $n:ident) => n.getId
    | _ => `_
  g.withContext do
    for n in names, fvar in xs do
      (Expr.fvar fvar).addLocalVarInfoForBinderIdent n
  return (ids, xs, g)
end Lean
namespace Mathlib.Tactic
syntax withArgs := " with" (ppSpace colGt ident)+
syntax usingArg := " using " term
open Lean Parser.Tactic
def getSimpArgs : Syntax → TacticM (Array Syntax)
  | `(simpArgs| [$args,*]) => pure args.getElems
  | _                      => Elab.throwUnsupportedSyntax
def getDSimpArgs : Syntax → TacticM (Array Syntax)
  | `(dsimpArgs| [$args,*]) => pure args.getElems
  | _                       => Elab.throwUnsupportedSyntax
def getWithArgs : Syntax → TacticM (Array Syntax)
  | `(withArgs| with $args*) => pure args
  | _                        => Elab.throwUnsupportedSyntax
def getUsingArg : Syntax → TacticM Syntax
  | `(usingArg| using $e) => pure e
  | _                     => Elab.throwUnsupportedSyntax
macro "repeat1 " seq:tacticSeq : tactic => `(tactic| (($seq); repeat $seq))
end Mathlib.Tactic
namespace Lean.Elab.Tactic
def filterOutImplementationDetails (lctx : LocalContext) (fvarIds : Array FVarId) : Array FVarId :=
  fvarIds.filter (fun fvar => ! (lctx.fvarIdToDecl.find! fvar).isImplementationDetail)
def getFVarIdAt (goal : MVarId) (id : Syntax) : TacticM FVarId := withRef id do
  let e ← goal.withContext do
    elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _                => throwError "unexpected term '{e}'; expected single reference to variable"
def getFVarIdsAt (goal : MVarId) (ids : Option (Array Syntax) := none)
    (includeImplementationDetails : Bool := false) : TacticM (Array FVarId) :=
  goal.withContext do
    let lctx := (← goal.getDecl).lctx
    let fvarIds ← match ids with
    | none => pure lctx.getFVarIds
    | some ids => ids.mapM <| getFVarIdAt goal
    if includeImplementationDetails then
      return fvarIds
    else
      return filterOutImplementationDetails lctx fvarIds
def allGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList
def andThenOnSubgoals (tac1 : TacticM Unit) (tac2 : TacticM Unit) : TacticM Unit :=
  focus do tac1; allGoals tac2
universe u
variable {m : Type → Type u} [Monad m] [MonadExcept Exception m]
def iterateAtMost : Nat → m Unit → m Unit
  | 0, _ => pure ()
  | n + 1, tac => try tac; iterateAtMost n tac catch _ => pure ()
def iterateExactly' : Nat → m Unit → m Unit
  | 0, _ => pure ()
  | n+1, tac => tac *> iterateExactly' n tac
def iterateRange : Nat → Nat → m Unit → m Unit
  | 0, 0, _   => pure ()
  | 0, b, tac => iterateAtMost b tac
  | (a+1), n, tac => do tac; iterateRange a (n-1) tac
partial def iterateUntilFailure (tac : m Unit) : m Unit :=
  try tac; iterateUntilFailure tac catch _ => pure ()
partial def iterateUntilFailureWithResults {α : Type} (tac : m α) : m (List α) := do
  try
    let a ← tac
    let l ← iterateUntilFailureWithResults tac
    pure (a :: l)
  catch _ => pure []
def iterateUntilFailureCount {α : Type} (tac : m α) : m Nat := do
  let r ← iterateUntilFailureWithResults tac
  return r.length
end Lean.Elab.Tactic
namespace Mathlib
open Lean
def getPackageDir (pkg : String) : IO System.FilePath := do
  let sp ← initSrcSearchPath
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
  throw <| IO.userError s!"Could not find {pkg} directory. \
    Make sure the LEAN_SRC_PATH environment variable is set correctly."
def getMathlibDir := getPackageDir "Mathlib"
end Mathlib