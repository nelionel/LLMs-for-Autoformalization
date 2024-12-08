import Lean
import Mathlib.Tactic.PPWithUniv
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.OldObtain
namespace Mathlib.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta
syntax (name := «variables») "variables" (ppSpace bracketedBinder)* : command
@[command_elab «variables»] def elabVariables : CommandElab
  | `(variables%$pos $binders*) => do
    logWarningAt pos "'variables' has been replaced by 'variable' in lean 4"
    elabVariable (← `(variable%$pos $binders*))
  | _ => throwUnsupportedSyntax
def pushFVarAliasInfo {m : Type → Type} [Monad m] [MonadInfoTree m]
    (oldFVars newFVars : Array FVarId) (newLCtx : LocalContext) : m Unit := do
  for old in oldFVars, new in newFVars do
    if old != new then
      let decl := newLCtx.get! new
      pushInfoLeaf (.ofFVarAliasInfo { id := new, baseId := old, userName := decl.userName })
syntax (name := introv) "introv " (ppSpace colGt binderIdent)* : tactic
@[tactic introv] partial def evalIntrov : Tactic := fun stx ↦ do
  match stx with
  | `(tactic| introv)                     => introsDep
  | `(tactic| introv $h:ident $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:binderIdent*))
  | `(tactic| introv _%$tk $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro _%$tk; introv $hs:binderIdent*))
  | _ => throwUnsupportedSyntax
where
  introsDep : TacticM Unit := do
    let t ← getMainTarget
    match t with
    | Expr.forallE _ _ e _ =>
      if e.hasLooseBVars then
        intro1PStep
        introsDep
    | _ => pure ()
  intro1PStep : TacticM Unit :=
    liftMetaTactic fun goal ↦ do
      let (_, goal) ← goal.intro1P
      pure [goal]
macro "assumption'" : tactic => `(tactic| any_goals assumption)
elab "match_target " t:term : tactic => do
  withMainContext do
    let (val) ← elabTerm t (← inferType (← getMainTarget))
    if not (← isDefEq val (← getMainTarget)) then
      throwError "failed"
elab (name := clearAuxDecl) "clear_aux_decl" : tactic => withMainContext do
  let mut g ← getMainGoal
  for ldec in ← getLCtx do
    if ldec.isAuxDecl then
      g ← g.tryClear ldec.fvarId
  replaceMainGoal [g]
def _root_.Lean.MVarId.clearValue (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  mvarId.checkNotAssigned `clear_value
  let tag ← mvarId.getTag
  let (_, mvarId) ← mvarId.withReverted #[fvarId] fun mvarId' fvars => mvarId'.withContext do
    let tgt ← mvarId'.getType
    unless tgt.isLet do
      mvarId.withContext <|
        throwTacticEx `clear_value mvarId m!"{Expr.fvar fvarId} is not a local definition"
    let tgt' := Expr.forallE tgt.letName! tgt.letType! tgt.letBody! .default
    unless ← isTypeCorrect tgt' do
      mvarId.withContext <|
        throwTacticEx `clear_value mvarId
          m!"cannot clear {Expr.fvar fvarId}, the resulting context is not type correct"
    let mvarId'' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
    mvarId'.assign <| .app mvarId'' tgt.letValue!
    return ((), fvars.map .some, mvarId''.mvarId!)
  return mvarId
elab (name := clearValue) "clear_value" hs:(ppSpace colGt term:max)+ : tactic => do
  let fvarIds ← getFVarIds hs
  let fvarIds ← withMainContext <| sortFVarIds fvarIds
  for fvarId in fvarIds.reverse do
    withMainContext do
      let mvarId ← (← getMainGoal).clearValue fvarId
      replaceMainGoal [mvarId]
attribute [pp_with_univ] ULift PUnit PEmpty
end Mathlib.Tactic