import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Basic
import Batteries.Tactic.Lint.Misc
open Lean Elab Parser Meta Tactic
def Lean.MVarId.extractLetsAt (mvarId : MVarId) (fvarId : FVarId) (names : Array Name) :
    MetaM (Array FVarId × MVarId) := do
  mvarId.checkNotAssigned `extractLetsAt
  mvarId.withReverted #[fvarId] fun mvarId fvarIds => mvarId.withContext do
    let mut mvarId := mvarId
    let mut fvarIds' := #[]
    for name in names do
      let ty ← Lean.instantiateMVars (← mvarId.getType)
      mvarId ← match ty with
        | .letE n t v b ndep => process mvarId t (.letE n · v b ndep)
        | .forallE n t v b   => process mvarId t (.forallE n · v b)
        | _ => throwTacticEx `extractLetsAt mvarId "unexpected auxiliary target"
      let (fvarId', mvarId') ← mvarId.intro name
      fvarIds' := fvarIds'.push fvarId'
      mvarId := mvarId'
    return (fvarIds', fvarIds.map .some, mvarId)
where
  process (mvarId : MVarId) (t : Expr) (mk : Expr → Expr) : MetaM MVarId := do
    let .letE n' t' v' b' _ := t.cleanupAnnotations
      | throwTacticEx `extractLetsAt mvarId "insufficient number of `let` expressions"
    withLetDecl n' t' v' fun fvar => do
      let b' := b'.instantiate1 fvar
      let ty' ← mkLetFVars (usedLetOnly := false) #[fvar] <| mk b'
      mvarId.change ty'
def Lean.MVarId.extractLets (mvarId : MVarId) (names : Array Name) :
    MetaM (Array FVarId × MVarId) :=
  mvarId.withContext do
    let ty := (← Lean.instantiateMVars (← mvarId.getType)).cleanupAnnotations
    if ty.letDepth < names.size then
      throwTacticEx `extractLets mvarId "insufficient number of `let` expressions"
    mvarId.introN names.size names.toList
namespace Mathlib
syntax (name := extractLets) "extract_lets " (colGt (ident <|> hole))* (ppSpace location)? : tactic
@[tactic Mathlib.extractLets, inherit_doc extractLets]
def evalExtractLets : Tactic := fun stx => do
  match stx with
  | `(tactic| extract_lets)                       => doExtract none none
  | `(tactic| extract_lets $hs*)                  => doExtract hs none
  | `(tactic| extract_lets $loc:location)         => doExtract none loc
  | `(tactic| extract_lets $hs* $loc:location)    => doExtract hs loc
  | _ => throwUnsupportedSyntax
where
  @[nolint docBlame]
  setupNames (ids? : Option (TSyntaxArray [`ident, `Lean.Parser.Term.hole])) (ty : Expr) :
      MetaM (Array Name) := do
    if let some ids := ids? then
      return ids.map getNameOfIdent'
    else
      return Array.mkArray (← instantiateMVars ty).cleanupAnnotations.letDepth `_
  @[nolint docBlame]
  doExtract (ids? : Option (TSyntaxArray [`ident, `Lean.Parser.Term.hole]))
      (loc? : Option <| TSyntax `Lean.Parser.Tactic.location) :
      TacticM Unit := do
    let process (f : MVarId → Array Name → MetaM (Array FVarId × MVarId))
        (ty : MVarId → MetaM Expr) : TacticM Unit := do
      let fvarIds ← liftMetaTacticAux fun mvarId => do
        let ids ← setupNames ids? (← ty mvarId)
        let (fvarIds, mvarId) ← f mvarId ids
        return (fvarIds, [mvarId])
      if let some ids := ids? then
        withMainContext do
          for stx in ids, fvarId in fvarIds do
            Term.addLocalVarInfo stx (.fvar fvarId)
    withLocation (expandOptLocation (mkOptionalNode loc?))
      (atLocal := fun h ↦ do
        process (fun mvarId ids => mvarId.extractLetsAt h ids) (fun _ => h.getType))
      (atTarget := do
        process (fun mvarId ids => mvarId.extractLets ids) (fun mvarId => mvarId.getType))
      (failed := fun _ ↦ throwError "extract_lets tactic failed")
end Mathlib