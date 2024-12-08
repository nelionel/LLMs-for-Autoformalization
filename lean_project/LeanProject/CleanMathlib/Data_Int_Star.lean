import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Star.Basic
open AddSubmonoid Set
namespace Int
@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn : Even n) :
    closure (range fun x : ℤ ↦ x ^ n) = nonneg _ := by
  refine le_antisymm (closure_le.2 <| range_subset_iff.2 hn.pow_nonneg) fun x hx ↦ ?_
  have : x = x.natAbs • 1 ^ n := by simpa [eq_comm (a := x)] using hx
  rw [this]
  exact nsmul_mem (subset_closure <| mem_range_self _) _
@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℤ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow even_two
instance instStarOrderedRing : StarOrderedRing ℤ where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]
end Int