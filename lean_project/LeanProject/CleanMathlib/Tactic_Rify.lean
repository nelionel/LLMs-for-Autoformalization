import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Qify
namespace Mathlib.Tactic.Rify
open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic
  linarith
```
`rify` makes use of the `@[zify_simps]`, `@[qify_simps]` and `@[rify_simps]` attributes to move
propositions, and the `push_cast` tactic to simplify the `ℝ`-valued expressions.
`rify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : a < b + c := by
  rify [hab] at h ⊢
  linarith
```
Note that `zify` or `qify` would work just as well in the above example (and `zify` is the natural
choice since it is enough to get rid of the pathological `ℕ` subtraction). -/
syntax (name := rify) "rify" (simpArgs)? (location)? : tactic
macro_rules
| `(tactic| rify $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    simp -decide only [zify_simps, qify_simps, rify_simps, push_cast, $args,*]
      $[at $location]?)
@[rify_simps] lemma ratCast_eq (a b : ℚ) : a = b ↔ (a : ℝ) = (b : ℝ) := by simp
@[rify_simps] lemma ratCast_le (a b : ℚ) : a ≤ b ↔ (a : ℝ) ≤ (b : ℝ) := by simp
@[rify_simps] lemma ratCast_lt (a b : ℚ) : a < b ↔ (a : ℝ) < (b : ℝ) := by simp
@[rify_simps] lemma ratCast_ne (a b : ℚ) : a ≠ b ↔ (a : ℝ) ≠ (b : ℝ) := by simp
@[deprecated (since := "2024-04-17")]
alias rat_cast_ne := ratCast_ne
@[rify_simps] lemma ofNat_rat_real (a : ℕ) [a.AtLeastTwo] :
    ((no_index (OfNat.ofNat a : ℚ)) : ℝ) = (OfNat.ofNat a : ℝ) := rfl
end Mathlib.Tactic.Rify