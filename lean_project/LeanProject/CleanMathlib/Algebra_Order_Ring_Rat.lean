import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
assert_not_exists Field
assert_not_exists Finset
assert_not_exists Set.Icc
assert_not_exists GaloisConnection
namespace Rat
instance instLinearOrderedCommRing : LinearOrderedCommRing ℚ where
  __ := Rat.linearOrder
  __ := Rat.commRing
  zero_le_one := by decide
  add_le_add_left := fun _ _ ab _ => Rat.add_le_add_left.2 ab
  mul_pos _ _ ha hb := (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')
instance : LinearOrderedRing ℚ := by infer_instance
instance : OrderedRing ℚ := by infer_instance
instance : LinearOrderedSemiring ℚ := by infer_instance
instance : OrderedSemiring ℚ := by infer_instance
instance : LinearOrderedAddCommGroup ℚ := by infer_instance
instance : OrderedAddCommGroup ℚ := by infer_instance
instance : OrderedCancelAddCommMonoid ℚ := by infer_instance
instance : OrderedAddCommMonoid ℚ := by infer_instance
end Rat