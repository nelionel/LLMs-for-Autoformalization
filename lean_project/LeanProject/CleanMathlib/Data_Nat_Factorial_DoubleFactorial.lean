import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity.Core
open Nat
namespace Nat
@[simp]
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (k + 2) * doubleFactorial k
@[inherit_doc] scoped notation:10000 n "‼" => Nat.doubleFactorial n
lemma doubleFactorial_pos : ∀ n, 0 < n‼
  | 0 | 1 => zero_lt_one
  | _n + 2 => mul_pos (succ_pos _) (doubleFactorial_pos _)
theorem doubleFactorial_add_two (n : ℕ) : (n + 2)‼ = (n + 2) * n‼ :=
  rfl
theorem doubleFactorial_add_one (n : ℕ) : (n + 1)‼ = (n + 1) * (n - 1)‼ := by cases n <;> rfl
theorem factorial_eq_mul_doubleFactorial : ∀ n : ℕ, (n + 1)! = (n + 1)‼ * n‼
  | 0 => rfl
  | k + 1 => by
    rw [doubleFactorial_add_two, factorial, factorial_eq_mul_doubleFactorial _, mul_comm _ k‼,
      mul_assoc]
lemma doubleFactorial_le_factorial : ∀ n, n‼ ≤ n !
  | 0 => le_rfl
  | n + 1 => by
    rw [factorial_eq_mul_doubleFactorial]; exact Nat.le_mul_of_pos_right _ n.doubleFactorial_pos
theorem doubleFactorial_two_mul : ∀ n : ℕ, (2 * n)‼ = 2 ^ n * n !
  | 0 => rfl
  | n + 1 => by
    rw [mul_add, mul_one, doubleFactorial_add_two, factorial, pow_succ, doubleFactorial_two_mul _,
      succ_eq_add_one]
    ring
theorem doubleFactorial_eq_prod_even : ∀ n : ℕ, (2 * n)‼ = ∏ i ∈ Finset.range n, 2 * (i + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, ← doubleFactorial_eq_prod_even _, mul_comm (2 * n)‼,
      (by ring : 2 * (n + 1) = 2 * n + 2)]
    rfl
theorem doubleFactorial_eq_prod_odd :
    ∀ n : ℕ, (2 * n + 1)‼ = ∏ i ∈ Finset.range n, (2 * (i + 1) + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, ← doubleFactorial_eq_prod_odd _, mul_comm (2 * n + 1)‼,
      (by ring : 2 * (n + 1) + 1 = 2 * n + 1 + 2)]
    rfl
end Nat
namespace Mathlib.Meta.Positivity
open Lean Meta Qq
@[positivity Nat.doubleFactorial _]
def evalDoubleFactorial : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.doubleFactorial $n) =>
    assumeInstancesCommute
    return .positive q(Nat.doubleFactorial_pos $n)
  | _, _ => throwError "not Nat.doubleFactorial"
example (n : ℕ) : 0 < n‼ := by positivity
end Mathlib.Meta.Positivity