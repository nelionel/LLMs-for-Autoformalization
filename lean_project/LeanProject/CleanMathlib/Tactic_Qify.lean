import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Zify
  sorry
```
-/
namespace Mathlib.Tactic.Qify
open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic
  sorry
```
`qify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℤ) (h : a / b = c) (hab : b ∣ a) (hb : b ≠ 0) : a = c * b := by
  qify [hab] at h hb ⊢
  exact (div_eq_iff hb).1 h
```
`qify` makes use of the `@[zify_simps]` and `@[qify_simps]` attributes to move propositions,
and the `push_cast` tactic to simplify the `ℚ`-valued expressions. -/
syntax (name := qify) "qify" (simpArgs)? (location)? : tactic
macro_rules
| `(tactic| qify $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    simp -decide only [zify_simps, qify_simps, push_cast, $args,*]
      $[at $location]?)
@[qify_simps] lemma intCast_eq (a b : ℤ) : a = b ↔ (a : ℚ) = (b : ℚ) := by simp only [Int.cast_inj]
@[qify_simps] lemma intCast_le (a b : ℤ) : a ≤ b ↔ (a : ℚ) ≤ (b : ℚ) := Int.cast_le.symm
@[qify_simps] lemma intCast_lt (a b : ℤ) : a < b ↔ (a : ℚ) < (b : ℚ) := Int.cast_lt.symm
@[qify_simps] lemma intCast_ne (a b : ℤ) : a ≠ b ↔ (a : ℚ) ≠ (b : ℚ) := by
  simp only [ne_eq, Int.cast_inj]
@[deprecated (since := "2024-04-17")]
alias int_cast_ne := intCast_ne
end Qify
end Mathlib.Tactic