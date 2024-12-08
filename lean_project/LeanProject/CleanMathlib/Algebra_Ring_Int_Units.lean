import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Units
assert_not_exists DenselyOrdered
assert_not_exists Set.Subsingleton
namespace Int
lemma units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff] using isUnit_eq_one_or u.isUnit
lemma units_ne_iff_eq_neg {u v : ℤˣ} : u ≠ v ↔ u = -v := by
  simpa only [Ne, Units.ext_iff] using isUnit_ne_iff_eq_neg u.isUnit v.isUnit
end Int