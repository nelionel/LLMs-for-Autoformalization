import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Order.Group.InjSurj
namespace Submodule
variable {R M : Type*}
section OrderedMonoid
variable [Semiring R]
instance toOrderedAddCommMonoid [OrderedAddCommMonoid M] [Module R M] (S : Submodule R M) :
    OrderedAddCommMonoid S :=
  Subtype.coe_injective.orderedAddCommMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl
instance toLinearOrderedAddCommMonoid [LinearOrderedAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommMonoid S :=
  Subtype.coe_injective.linearOrderedAddCommMonoid Subtype.val rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
instance toOrderedCancelAddCommMonoid [OrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : OrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.orderedCancelAddCommMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl
instance toLinearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.linearOrderedCancelAddCommMonoid Subtype.val rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
end OrderedMonoid
section OrderedGroup
variable [Ring R]
instance toOrderedAddCommGroup [OrderedAddCommGroup M] [Module R M] (S : Submodule R M) :
    OrderedAddCommGroup S :=
  Subtype.coe_injective.orderedAddCommGroup Subtype.val rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
instance toLinearOrderedAddCommGroup [LinearOrderedAddCommGroup M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommGroup S :=
  Subtype.coe_injective.linearOrderedAddCommGroup Subtype.val rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
end OrderedGroup
end Submodule