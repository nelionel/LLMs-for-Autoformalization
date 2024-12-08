import Mathlib.Algebra.Order.Field.InjSurj
import Mathlib.Algebra.Field.Subfield.Defs
namespace SubfieldClass
variable {K S : Type*} [SetLike S K]
instance (priority := 75) toLinearOrderedField [LinearOrderedField K]
    [SubfieldClass S K] (s : S) : LinearOrderedField s :=
  Subtype.coe_injective.linearOrderedField Subtype.val rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (by intros; rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by intros; rfl) (fun _ _ => rfl) fun _ _ => rfl
end SubfieldClass
namespace Subfield
variable {K : Type*}
instance toLinearOrderedField [LinearOrderedField K] (s : Subfield K) : LinearOrderedField s :=
  Subtype.coe_injective.linearOrderedField Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (by intros; rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by intros; rfl) (fun _ _ => rfl) fun _ _ => rfl
end Subfield