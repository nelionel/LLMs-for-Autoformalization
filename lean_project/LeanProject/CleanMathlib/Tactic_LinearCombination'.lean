import Mathlib.Tactic.Ring
namespace Mathlib.Tactic.LinearCombination'
open Lean
open Elab Meta Term
variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}
theorem pf_add_c [Add α] (p : a = b) (c : α) : a + c = b + c := p ▸ rfl
theorem c_add_pf [Add α] (p : b = c) (a : α) : a + b = a + c := p ▸ rfl
theorem add_pf [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl
theorem pf_sub_c [Sub α] (p : a = b) (c : α) : a - c = b - c := p ▸ rfl
theorem c_sub_pf [Sub α] (p : b = c) (a : α) : a - b = a - c := p ▸ rfl
theorem sub_pf [Sub α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ - a₂ = b₁ - b₂ := p₁ ▸ p₂ ▸ rfl
theorem neg_pf [Neg α] (p : (a:α) = b) : -a = -b := p ▸ rfl
theorem pf_mul_c [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl
theorem c_mul_pf [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl
theorem mul_pf [Mul α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ * a₂ = b₁ * b₂ := p₁ ▸ p₂ ▸ rfl
theorem inv_pf [Inv α] (p : (a:α) = b) : a⁻¹ = b⁻¹ := p ▸ rfl
theorem pf_div_c [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl
theorem c_div_pf [Div α] (p : b = c) (a : α) : a / b = a / c := p ▸ rfl
theorem div_pf [Div α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ / a₂ = b₁ / b₂ := p₁ ▸ p₂ ▸ rfl
inductive Expanded
  | proof (pf : Syntax.Term)
  | const (c : Syntax.Term)
partial def expandLinearCombo (ty : Expr) (stx : Syntax.Term) : TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_add_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_add_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(add_pf $p₁ $p₂)
  | `($e₁ - $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_sub_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_sub_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(sub_pf $p₁ $p₂)
  | `(-$e) => do
    match ← expandLinearCombo ty e with
    | .const c => .const <$> `(-$c)
    | .proof p => .proof <$> ``(neg_pf $p)
  | `(← $e) => do
    match ← expandLinearCombo ty e with
    | .const c => return .const c
    | .proof p => .proof <$> ``(Eq.symm $p)
  | `($e₁ * $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ * $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_mul_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_mul_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(mul_pf $p₁ $p₂)
  | `($e⁻¹) => do
    match ← expandLinearCombo ty e with
    | .const c => .const <$> `($c⁻¹)
    | .proof p => .proof <$> ``(inv_pf $p)
  | `($e₁ / $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_div_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_div_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(div_pf $p₁ $p₂)
  | e =>
    withSynthesize do
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      if (← whnfR (← inferType c)).isEq then
        .proof <$> c.toSyntax
      else
        .const <$> c.toSyntax
theorem eq_trans₃ (p : (a:α) = b) (p₁ : a = a') (p₂ : b = b') : a' = b' := p₁ ▸ p₂ ▸ p
theorem eq_of_add [AddGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; rwa [sub_eq_zero, p] at H
theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H
def elabLinearCombination' (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term)
    (twoGoals := false) : Tactic.TacticM Unit := Tactic.withMainContext do
  let some (ty, _) := (← (← Tactic.getMainGoal).getType').eq? |
    throwError "'linear_combination'' only proves equalities"
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e =>
    match ← expandLinearCombo ty e with
    | .const c => `(Eq.refl $c)
    | .proof p => pure p
  let norm := norm?.getD (Unhygienic.run <| withRef tk `(tactic| ring1))
  Term.withoutErrToSorry <| Tactic.evalTactic <| ← withFreshMacroScope <|
  if twoGoals then
    `(tactic| (
      refine eq_trans₃ $p ?a ?b
      case' a => $norm:tactic
      case' b => $norm:tactic))
  else
    match exp? with
    | some n =>
      if n.getNat = 1 then `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))
      else `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
    | _ => `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))
syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"
syntax expStx := atomic(" (" &"exp" " := ") withoutPosition(num) ")"
example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination' ha - hb - 2*hc
example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination' x*y*h1 + 2*h2
example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination' (norm := skip) 2*h1
  simp
axiom qc : ℚ
axiom hqc : qc = 2*qc
example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination' 3 * h a b + hqc
```
-/
syntax (name := linearCombination') "linear_combination'"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination'%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabLinearCombination' tk tac n e
@[inherit_doc linearCombination']
syntax "linear_combination2" (normStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination2%$tk $[(norm := $tac)]? $(e)?) =>
    elabLinearCombination' tk tac none e true
end Mathlib.Tactic.LinearCombination'