import Lean.Elab.Tactic.Location
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Conv
namespace Mathlib.Tactic.PushNeg
open Lean Meta Elab.Tactic Parser.Tactic
variable (p q : Prop) {α : Sort*} {β : Type*} (s : α → Prop)
theorem not_not_eq : (¬ ¬ p) = p := propext not_not
theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_or
theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext Classical.not_imp
theorem not_ne_eq (x y : α) : (¬ (x ≠ y)) = (x = y) := ne_eq x y ▸ not_not_eq _
theorem not_iff : (¬ (p ↔ q)) = ((p ∧ ¬ q) ∨ (¬ p ∧ q)) := propext <|
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]
section LinearOrder
variable [LinearOrder β]
theorem not_le_eq (a b : β) : (¬ (a ≤ b)) = (b < a) := propext not_le
theorem not_lt_eq (a b : β) : (¬ (a < b)) = (b ≤ a) := propext not_lt
theorem not_ge_eq (a b : β) : (¬ (a ≥ b)) = (a < b) := propext not_le
theorem not_gt_eq (a b : β) : (¬ (a > b)) = (a ≤ b) := propext not_lt
end LinearOrder
theorem not_nonempty_eq (s : Set β) : (¬ s.Nonempty) = (s = ∅) := by
  have A : ∀ (x : β), ¬(x ∈ (∅ : Set β)) := fun x ↦ id
  simp only [Set.Nonempty, not_exists, eq_iff_iff]
  exact ⟨fun h ↦ Set.ext (fun x ↦ by simp only [h x, false_iff, A]), fun h ↦ by rwa [h]⟩
theorem ne_empty_eq_nonempty (s : Set β) : (s ≠ ∅) = s.Nonempty := by
  rw [ne_eq, ← not_nonempty_eq s, not_not]
theorem empty_ne_eq_nonempty (s : Set β) : (∅ ≠ s) = s.Nonempty := by
  rw [ne_comm, ne_empty_eq_nonempty]
register_option push_neg.use_distrib : Bool :=
  { defValue := false
    group := ""
    descr := "Make `push_neg` use `not_and_or` rather than the default `not_and`." }
def transformNegationStep (e : Expr) : SimpM (Option Simp.Step) := do
  let mkSimpStep (e : Expr) (pf : Expr) : Simp.Step :=
    Simp.Step.visit { expr := e, proof? := some pf }
  let handleIneq (e₁ e₂ : Expr) (notThm : Name) : SimpM (Option Simp.Step) := do
    try
      let thm ← mkAppM notThm #[e₁, e₂]
      let some (_, lhs, rhs) := (← inferType thm).eq? | failure 
      guard <| ← isDefEq e lhs
      return some <| mkSimpStep rhs thm
    catch _ => return none
  let e_whnf ← whnfR e
  let some ex := e_whnf.not? | return Simp.Step.continue
  let ex := (← instantiateMVars ex).cleanupAnnotations
  match ex.getAppFnArgs with
  | (``Not, #[e]) =>
      return mkSimpStep e (← mkAppM ``not_not_eq #[e])
  | (``And, #[p, q]) =>
      match ← getBoolOption `push_neg.use_distrib with
      | false => return mkSimpStep (.forallE `_ p (mkNot q) default) (← mkAppM ``not_and_eq #[p, q])
      | true  => return mkSimpStep (mkOr (mkNot p) (mkNot q)) (← mkAppM ``not_and_or_eq #[p, q])
  | (``Or, #[p, q]) =>
      return mkSimpStep (mkAnd (mkNot p) (mkNot q)) (← mkAppM ``not_or_eq #[p, q])
  | (``Iff, #[p, q]) =>
      return mkSimpStep (mkOr (mkAnd p (mkNot q)) (mkAnd (mkNot p) q)) (← mkAppM ``not_iff #[p, q])
  | (``Eq, #[ty, e₁, e₂]) =>
      if ty.isAppOfArity ``Set 1 then
        if e₂.isAppOfArity ``EmptyCollection.emptyCollection 2 then
          let thm ← mkAppM ``ne_empty_eq_nonempty #[e₁]
          let some (_, _, rhs) := (← inferType thm).eq? | return none
          return mkSimpStep rhs thm
        if e₁.isAppOfArity ``EmptyCollection.emptyCollection 2 then
          let thm ← mkAppM ``empty_ne_eq_nonempty #[e₂]
          let some (_, _, rhs) := (← inferType thm).eq? | return none
          return mkSimpStep rhs thm
      return Simp.Step.visit { expr := ← mkAppM ``Ne #[e₁, e₂] }
  | (``Ne, #[_ty, e₁, e₂]) =>
      return mkSimpStep (← mkAppM ``Eq #[e₁, e₂]) (← mkAppM ``not_ne_eq #[e₁, e₂])
  | (``LE.le, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_le_eq
  | (``LT.lt, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_lt_eq
  | (``GE.ge, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_ge_eq
  | (``GT.gt, #[_ty, _inst, e₁, e₂]) => handleIneq e₁ e₂ ``not_gt_eq
  | (``Set.Nonempty, #[_ty, e]) =>
      let thm ← mkAppM ``not_nonempty_eq #[e]
      let some (_, _, rhs) := (← inferType thm).eq? | return none
      return mkSimpStep rhs thm
  | (``Exists, #[_, .lam n typ bo bi]) =>
      return mkSimpStep (.forallE n typ (mkNot bo) bi)
                        (← mkAppM ``not_exists_eq #[.lam n typ bo bi])
  | (``Exists, #[_, _]) =>
      return none
  | _ => match ex with
          | .forallE name ty body binfo => do
              if (← isProp ty) && !body.hasLooseBVars then
                return mkSimpStep (← mkAppM ``And #[ty, mkNot body])
                  (← mkAppM ``not_implies_eq #[ty, body])
              else
                let body' : Expr := .lam name ty (mkNot body) binfo
                let body'' : Expr := .lam name ty body binfo
                return mkSimpStep (← mkAppM ``Exists #[body']) (← mkAppM ``not_forall_eq #[body''])
          | _ => return none
partial def transformNegation (e : Expr) : SimpM Simp.Step := do
  let Simp.Step.visit r₁ ← transformNegationStep e | return Simp.Step.continue
  match r₁.proof? with
  | none => return Simp.Step.continue r₁
  | some _ => do
      let Simp.Step.visit r₂ ← transformNegation r₁.expr | return Simp.Step.visit r₁
      return Simp.Step.visit (← r₁.mkEqTrans r₂)
def pushNegCore (tgt : Expr) : MetaM Simp.Result := do
  let myctx : Simp.Context ← Simp.mkContext { eta := true, zeta := false, proj := false }
      (simpTheorems := #[ ])
      (congrTheorems := (← getSimpCongrTheorems))
  (·.1) <$> Simp.main tgt myctx (methods := { pre := transformNegation })
syntax (name := pushNegConv) "push_neg" : conv
@[tactic pushNegConv] def elabPushNegConv : Tactic := fun _ ↦ withMainContext do
  Conv.applySimpResult (← pushNegCore (← instantiateMVars (← Conv.getLhs)))
macro (name := pushNeg) tk:"#push_neg " e:term : command => `(command| #conv%$tk push_neg => $e)
def pushNegTarget : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let newGoal ← applySimpResultToTarget goal tgt (← pushNegCore tgt)
  if newGoal == goal then throwError "push_neg made no progress"
  replaceMainGoal [newGoal]
def pushNegLocalDecl (fvarId : FVarId) : TacticM Unit := withMainContext do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt ← instantiateMVars ldecl.type
  let goal ← getMainGoal
  let myres ← pushNegCore tgt
  let some (_, newGoal) ← applySimpResultToLocalDecl goal fvarId myres False | failure
  if newGoal == goal then throwError "push_neg made no progress"
  replaceMainGoal [newGoal]
elab "push_neg" loc:(location)? : tactic =>
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  withLocation loc
    pushNegLocalDecl
    pushNegTarget
    (fun _ ↦ logInfo "push_neg couldn't find a negation to push")
end Mathlib.Tactic.PushNeg