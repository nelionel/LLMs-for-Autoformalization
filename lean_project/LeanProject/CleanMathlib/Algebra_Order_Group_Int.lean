import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Order.Group.Defs
assert_not_exists Set.Subsingleton
assert_not_exists Ring
open Function Nat
namespace Int
instance linearOrderedAddCommGroup : LinearOrderedAddCommGroup ℤ where
  __ := instLinearOrder
  __ := instAddCommGroup
  add_le_add_left _ _ := Int.add_le_add_left
end Int