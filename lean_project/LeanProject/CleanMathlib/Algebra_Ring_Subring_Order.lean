import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Ring.Subring.Defs
namespace SubringClass
variable {R S : Type*} [SetLike S R] (s : S)
instance (priority := 75) toOrderedRing [OrderedRing R] [SubringClass S R] :
    OrderedRing s :=
  Subtype.coe_injective.orderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl
instance (priority := 75) toOrderedCommRing [OrderedCommRing R] [SubringClass S R] :
    OrderedCommRing s :=
  Subtype.coe_injective.orderedCommRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl
instance (priority := 75) toLinearOrderedRing [LinearOrderedRing R] [SubringClass S R] :
    LinearOrderedRing s :=
  Subtype.coe_injective.linearOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
instance (priority := 75) toLinearOrderedCommRing [LinearOrderedCommRing R] [SubringClass S R] :
    LinearOrderedCommRing s :=
  Subtype.coe_injective.linearOrderedCommRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
end SubringClass
namespace Subring
variable {R : Type*}
instance toOrderedRing [OrderedRing R] (s : Subring R) : OrderedRing s :=
  SubringClass.toOrderedRing s
instance toOrderedCommRing [OrderedCommRing R] (s : Subring R) : OrderedCommRing s :=
  SubringClass.toOrderedCommRing s
instance toLinearOrderedRing [LinearOrderedRing R] (s : Subring R) : LinearOrderedRing s :=
  SubringClass.toLinearOrderedRing s
instance toLinearOrderedCommRing [LinearOrderedCommRing R] (s : Subring R) :
    LinearOrderedCommRing s :=
  SubringClass.toLinearOrderedCommRing s
def orderedSubtype {R : Type*} [OrderedRing R] (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h
variable {R : Type*} [OrderedRing R]
lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl
end Subring