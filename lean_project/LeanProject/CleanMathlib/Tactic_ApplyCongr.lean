import Mathlib.Tactic.Conv
open Lean Expr Parser.Tactic Elab Command Elab.Tactic Meta Conv
def Lean.Elab.Tactic.applyCongr (q : Option Expr) : TacticM Unit := do
  let const lhsFun _ ← (getAppFn ∘ cleanupAnnotations) <$> instantiateMVars (← getLhs) |
    throwError "Left-hand side must be an application of a constant."
  let congrTheoremExprs ←
    match q with
    | some e =>
      pure [e]
    | none =>
      let congrTheorems ←
        (fun congrTheoremMap => congrTheoremMap.get lhsFun) <$> getSimpCongrTheorems
      congrTheorems.mapM (fun congrTheorem =>
        liftM <| mkConstWithFreshMVarLevels congrTheorem.theoremName)
  if congrTheoremExprs == [] then
    throwError "No matching congr lemmas found"
  liftMetaTactic fun mainGoal => congrTheoremExprs.firstM (fun congrTheoremExpr => do
    let newGoals ← mainGoal.apply congrTheoremExpr { newGoals := .nonDependentOnly }
    newGoals.mapM fun newGoal => Prod.snd <$> newGoal.intros)
syntax (name := Lean.Parser.Tactic.applyCongr) "apply_congr" (ppSpace colGt term)? : conv
elab_rules : conv
  | `(conv| apply_congr$[ $t?]?) => do
    let e? ← t?.mapM (fun t => elabTerm t.raw none)
    applyCongr e?