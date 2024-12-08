import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
open Function
variable {α : Type*}
class OrderedAddCommMonoid (α : Type*) extends AddCommMonoid α, PartialOrder α where
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b
@[to_additive]
class OrderedCommMonoid (α : Type*) extends CommMonoid α, PartialOrder α where
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b
section OrderedCommMonoid
variable [OrderedCommMonoid α]
@[to_additive]
instance OrderedCommMonoid.toMulLeftMono : MulLeftMono α where
  elim := fun a _ _ bc ↦ OrderedCommMonoid.mul_le_mul_left _ _ bc a
@[to_additive]
theorem OrderedCommMonoid.toMulRightMono (M : Type*) [OrderedCommMonoid M] :
    MulRightMono M :=
  inferInstance
end OrderedCommMonoid
class OrderedCancelAddCommMonoid (α : Type*) extends OrderedAddCommMonoid α where
  protected le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c
@[to_additive OrderedCancelAddCommMonoid]
class OrderedCancelCommMonoid (α : Type*) extends OrderedCommMonoid α where
  protected le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c
section OrderedCancelCommMonoid
variable [OrderedCancelCommMonoid α]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.toMulLeftReflectLE :
    MulLeftReflectLE α :=
  ⟨OrderedCancelCommMonoid.le_of_mul_le_mul_left⟩
@[to_additive]
instance OrderedCancelCommMonoid.toMulLeftReflectLT :
    MulLeftReflectLT α where
  elim := contravariant_lt_of_contravariant_le α α _ ContravariantClass.elim
@[to_additive]
theorem OrderedCancelCommMonoid.toMulRightReflectLT :
    MulRightReflectLT α :=
  inferInstance
@[to_additive OrderedCancelAddCommMonoid.toCancelAddCommMonoid]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    mul_left_cancel :=
      fun _ _ _ h => (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge }
end OrderedCancelCommMonoid
class LinearOrderedAddCommMonoid (α : Type*) extends OrderedAddCommMonoid α, LinearOrder α
@[to_additive]
class LinearOrderedCommMonoid (α : Type*) extends OrderedCommMonoid α, LinearOrder α
class LinearOrderedCancelAddCommMonoid (α : Type*) extends OrderedCancelAddCommMonoid α,
    LinearOrderedAddCommMonoid α
@[to_additive LinearOrderedCancelAddCommMonoid]
class LinearOrderedCancelCommMonoid (α : Type*) extends OrderedCancelCommMonoid α,
    LinearOrderedCommMonoid α
attribute [to_additive existing] LinearOrderedCancelCommMonoid.toLinearOrderedCommMonoid
variable [LinearOrderedCommMonoid α] {a : α}
@[to_additive (attr := simp)]
theorem one_le_mul_self_iff : 1 ≤ a * a ↔ 1 ≤ a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_lt_one' h h).mtr, fun h ↦ one_le_mul h h⟩
@[to_additive (attr := simp)]
theorem one_lt_mul_self_iff : 1 < a * a ↔ 1 < a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_le_one' h h).mtr, fun h ↦ one_lt_mul'' h h⟩
@[to_additive (attr := simp)]
theorem mul_self_le_one_iff : a * a ≤ 1 ↔ a ≤ 1 := by simp [← not_iff_not]
@[to_additive (attr := simp)]
theorem mul_self_lt_one_iff : a * a < 1 ↔ a < 1 := by simp [← not_iff_not]