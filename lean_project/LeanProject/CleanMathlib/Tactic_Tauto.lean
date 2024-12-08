import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Core
import Mathlib.Lean.Elab.Tactic.Basic
import Mathlib.Logic.Basic
import Qq
namespace Mathlib.Tactic.Tauto
open Lean Elab.Tactic Parser.Tactic Lean.Meta MVarId Batteries.Tactic
open Qq
initialize registerTraceClass `tauto
def distribNotOnceAt (hypFVar : Expr) (g : MVarId) : MetaM AssertAfterResult := g.withContext do
  let .fvar fvarId := hypFVar | throwError "not fvar {hypFVar}"
  let h ← fvarId.getDecl
  let e : Q(Prop) ← (do guard <| ← Meta.isProp h.type; pure h.type)
  let replace (p : Expr) : MetaM AssertAfterResult := do
    commitIfNoEx do
      let result ← g.assertAfter fvarId h.userName (← inferType p) p
      let newGoal ← result.mvarId.clear fvarId
      return { result with mvarId := newGoal }
  match e with
  | ~q(¬ ($a : Prop) = $b) => do
    let h' : Q(¬$a = $b) := h.toExpr
    replace q(mt propext $h')
  | ~q(($a : Prop) = $b) => do
    let h' : Q($a = $b) := h.toExpr
    replace q(Eq.to_iff $h')
  | ~q(¬ (($a : Prop) ∧ $b)) => do
    let h' : Q(¬($a ∧ $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
    replace q(Decidable.not_and_iff_or_not_not'.mp $h')
  | ~q(¬ (($a : Prop) ∨ $b)) => do
    let h' : Q(¬($a ∨ $b)) := h.toExpr
    replace q(not_or.mp $h')
  | ~q(¬ (($a : Prop) ≠ $b)) => do
    let h' : Q(¬($a ≠ $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable ($a = $b)) : Q(Type))
    replace q(Decidable.of_not_not $h')
  | ~q(¬¬ ($a : Prop)) => do
    let h' : Q(¬¬$a) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
    replace q(Decidable.of_not_not $h')
  | ~q(¬ ((($a : Prop)) → $b)) => do
    let h' : Q(¬($a → $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
    replace q(Decidable.not_imp_iff_and_not.mp $h')
  | ~q(¬ (($a : Prop) ↔ $b)) => do
    let h' : Q(¬($a ↔ $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
    replace q(Decidable.not_iff.mp $h')
  | ~q(($a : Prop) ↔ $b) => do
    let h' : Q($a ↔ $b) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
    replace q(Decidable.iff_iff_and_or_not_and_not.mp $h')
  | ~q((((($a : Prop)) → False) : Prop)) =>
    throwError "distribNot found nothing to work on with negation"
  | ~q((((($a : Prop)) → $b) : Prop)) => do
    let h' : Q($a → $b) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
    replace q(Decidable.not_or_of_imp $h')
  | _ => throwError "distribNot found nothing to work on"
structure DistribNotState where
  fvars : List Expr
  currentGoal : MVarId
partial def distribNotAt (nIters : Nat) (state : DistribNotState) : MetaM DistribNotState :=
  match nIters, state.fvars with
  | 0, _ | _, [] => pure state
  | n + 1, fv::fvs => do
    try
      let result ← distribNotOnceAt fv state.currentGoal
      let newFVars := mkFVar result.fvarId :: fvs.map (fun x ↦ result.subst.apply x)
      distribNotAt n ⟨newFVars, result.mvarId⟩
    catch _ => pure state
partial def distribNotAux (fvars : List Expr) (g : MVarId) : MetaM MVarId :=
  match fvars with
  | [] => pure g
  | _ => do
    let result ← distribNotAt 3 ⟨fvars, g⟩
    distribNotAux result.fvars.tail! result.currentGoal
def distribNot : TacticM Unit := withMainContext do
  let mut fvars := []
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      fvars := mkFVar h.fvarId :: fvars
  liftMetaTactic' (distribNotAux fvars)
structure Config
declare_config_elab elabConfig Config
def coreConstructorMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(True) => pure true
  | _ => pure false
def casesMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ∨ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(False) => pure true
  | _ => pure false
@[inherit_doc]
local infixl: 50 " <;> " => andThenOnSubgoals
def tautoCore : TacticM Unit := do
  _ ← tryTactic (evalTactic (← `(tactic| contradiction)))
  _ ← tryTactic (evalTactic (← `(tactic| assumption)))
  iterateUntilFailure do
    let gs ← getUnsolvedGoals
    allGoals (
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      distribNot <;>
      liftMetaTactic (casesMatching casesMatcher (recursive := true) (throwOnNoMatch := false)) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| contradiction)))) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| refine or_iff_not_imp_left.mpr ?_)))) <;>
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · coreConstructorMatcher
        (recursive := true) (throwOnNoMatch := false)) <;>
      do _ ← tryTactic (evalTactic (← `(tactic| assumption))))
    let gs' ← getUnsolvedGoals
    if gs == gs' then failure 
    pure ()
def finishingConstructorMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(True) => pure true
  | _ => pure false
def tautology : TacticM Unit := focusAndDoneWithScope "tauto" do
  classical do
    tautoCore
    allGoals (iterateUntilFailure
      (evalTactic (← `(tactic| rfl)) <|>
      evalTactic (← `(tactic| solve_by_elim)) <|>
      liftMetaTactic (constructorMatching · finishingConstructorMatcher)))
syntax (name := tauto) "tauto" optConfig : tactic
elab_rules : tactic | `(tactic| tauto $cfg:optConfig) => do
  let _cfg ← elabConfig cfg
  tautology
end Mathlib.Tactic.Tauto