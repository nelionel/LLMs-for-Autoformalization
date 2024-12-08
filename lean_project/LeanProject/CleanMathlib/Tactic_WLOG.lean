import Mathlib.Tactic.Core
import Lean.Meta.Tactic.Cases
namespace Mathlib.Tactic
open Lean Meta Elab Term Tactic MetavarContext.MkBinding
structure WLOGResult where
  reductionGoal    : MVarId
  reductionFVarIds : FVarId × FVarId
  hypothesisGoal   : MVarId
  hypothesisFVarId : FVarId
  revertedFVarIds  : Array FVarId
open private withFreshCache mkAuxMVarType from Lean.MetavarContext in
def _root_.Lean.MVarId.wlog (goal : MVarId) (h : Option Name) (P : Expr)
    (xs : Option (TSyntaxArray `ident) := none) (H : Option Name := none) :
    TacticM WLOGResult := goal.withContext do
  goal.checkNotAssigned `wlog
  let H := H.getD `this
  let inaccessible := h.isNone
  let h := h.getD `h
  let HSuffix := Expr.forallE h P (← goal.getType) .default
  let fvars ← getFVarIdsAt goal xs
  let fvars := fvars.map Expr.fvar
  let lctx := (← goal.getDecl).lctx
  let (revertedFVars, HType) ← liftMkBindingM fun ctx => (do
    let f ← collectForwardDeps lctx fvars
    let revertedFVars := filterOutImplementationDetails lctx (f.map Expr.fvarId!)
    let HType ← withFreshCache do
      mkAuxMVarType lctx (revertedFVars.map Expr.fvar) .natural HSuffix (usedLetOnly := true)
    return (revertedFVars, HType))
      { preserveOrder := false, mainModule := ctx.mainModule }
  let HExpr ← mkFreshExprSyntheticOpaqueMVar HType
  let hGoal := HExpr.mvarId!
  let (HFVarId, reductionGoal) ←
    goal.assertHypotheses #[{ userName := H, type := HType, value := HExpr }]
  let HFVarId := HFVarId[0]!
  let hGoal ← hGoal.tryClearMany revertedFVars
  let (_, hGoal) ← hGoal.introNP revertedFVars.size
  let (hFVar, hGoal) ← if inaccessible then hGoal.intro1 else hGoal.intro1P
  let (⟨easyGoal, hyp⟩, ⟨reductionGoal, negHyp⟩) ←
    reductionGoal.byCases P <| if inaccessible then `_ else h
  easyGoal.withContext do
    let HArgFVarIds ← revertedFVars.filterM (notM ·.isLetVar)
    let HApp ← instantiateMVars <|
      mkAppN (.fvar HFVarId) (HArgFVarIds.map .fvar) |>.app (.fvar hyp)
    ensureHasNoMVars HApp
    easyGoal.assign HApp
  return ⟨reductionGoal, (HFVarId, negHyp), hGoal, hFVar, revertedFVars⟩
syntax (name := wlog) "wlog " binderIdent " : " term
  (" generalizing" (ppSpace colGt ident)*)? (" with " binderIdent)? : tactic
elab_rules : tactic
| `(tactic| wlog $h:binderIdent : $P:term $[ generalizing $xs*]? $[ with $H:ident]?) =>
  withMainContext do
  let H := H.map (·.getId)
  let h := match h with
  | `(binderIdent|$h:ident) => some h.getId
  | _ => none
  let P ← elabType P
  let goal ← getMainGoal
  let { reductionGoal, hypothesisGoal .. } ← goal.wlog h P xs H
  replaceMainGoal [reductionGoal, hypothesisGoal]
end Mathlib.Tactic