import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Canonical
variable {α : Type*}
class CanonicallyLinearOrderedSemifield (α : Type*) extends CanonicallyOrderedCommSemiring α,
  LinearOrderedSemifield α
instance (priority := 100) CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero
    [CanonicallyLinearOrderedSemifield α] : LinearOrderedCommGroupWithZero α :=
  { ‹CanonicallyLinearOrderedSemifield α› with
    mul_le_mul_left := fun _ _ h _ ↦ mul_le_mul_of_nonneg_left h <| zero_le _ }
instance (priority := 100) CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddCommMonoid
    [CanonicallyLinearOrderedSemifield α] : CanonicallyLinearOrderedAddCommMonoid α :=
  { ‹CanonicallyLinearOrderedSemifield α› with }