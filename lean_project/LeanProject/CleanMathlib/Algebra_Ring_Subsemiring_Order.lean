import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Order.Interval.Set.Defs
namespace SubsemiringClass
variable {R S : Type*} [SetLike S R] (s : S)
instance toOrderedSemiring [OrderedSemiring R] [SubsemiringClass S R] :
    OrderedSemiring s :=
  Subtype.coe_injective.orderedSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toStrictOrderedSemiring [StrictOrderedSemiring R]
    [SubsemiringClass S R] : StrictOrderedSemiring s :=
  Subtype.coe_injective.strictOrderedSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toOrderedCommSemiring [OrderedCommSemiring R] [SubsemiringClass S R] :
    OrderedCommSemiring s :=
  Subtype.coe_injective.orderedCommSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toStrictOrderedCommSemiring [StrictOrderedCommSemiring R]
    [SubsemiringClass S R] : StrictOrderedCommSemiring s :=
  Subtype.coe_injective.strictOrderedCommSemiring Subtype.val rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toLinearOrderedSemiring [LinearOrderedSemiring R]
    [SubsemiringClass S R] : LinearOrderedSemiring s :=
  Subtype.coe_injective.linearOrderedSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
instance toLinearOrderedCommSemiring [LinearOrderedCommSemiring R]
    [SubsemiringClass S R] : LinearOrderedCommSemiring s :=
  Subtype.coe_injective.linearOrderedCommSemiring Subtype.val rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl
end SubsemiringClass
namespace Subsemiring
variable {R : Type*}
instance toOrderedSemiring [OrderedSemiring R] (s : Subsemiring R) : OrderedSemiring s :=
  Subtype.coe_injective.orderedSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toStrictOrderedSemiring [StrictOrderedSemiring R] (s : Subsemiring R) :
    StrictOrderedSemiring s :=
  Subtype.coe_injective.strictOrderedSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toOrderedCommSemiring [OrderedCommSemiring R] (s : Subsemiring R) :
    OrderedCommSemiring s :=
  Subtype.coe_injective.orderedCommSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toStrictOrderedCommSemiring [StrictOrderedCommSemiring R] (s : Subsemiring R) :
    StrictOrderedCommSemiring s :=
  Subtype.coe_injective.strictOrderedCommSemiring Subtype.val rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
instance toLinearOrderedSemiring [LinearOrderedSemiring R] (s : Subsemiring R) :
    LinearOrderedSemiring s :=
  Subtype.coe_injective.linearOrderedSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
instance toLinearOrderedCommSemiring [LinearOrderedCommSemiring R] (s : Subsemiring R) :
    LinearOrderedCommSemiring s :=
  Subtype.coe_injective.linearOrderedCommSemiring Subtype.val rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl
@[simps]
def nonneg (R : Type*) [OrderedSemiring R] : Subsemiring R where
  carrier := Set.Ici 0
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one
  add_mem' := add_nonneg
  zero_mem' := le_rfl
end Subsemiring