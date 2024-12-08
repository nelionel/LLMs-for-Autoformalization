import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
variable {M : Type*} [CancelCommMonoidWithZero M]
namespace Associates
instance instOrderedCommMonoid : OrderedCommMonoid (Associates M) where
  mul_le_mul_left := fun a _ ⟨d, hd⟩ c => hd.symm ▸ mul_assoc c a d ▸ le_mul_right
instance : CanonicallyOrderedCommMonoid (Associates M) where
  exists_mul_of_le h := h
  le_self_mul _ b := ⟨b, rfl⟩
  bot_le _ := one_le
end Associates