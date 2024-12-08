import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
variable {C : Type u₁}
section
variable [CategoryStruct.{v₁} C] [Quiver.IsThin C]
def thin_category : Category C where
end
variable [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable [Quiver.IsThin C]
instance functor_thin : Quiver.IsThin (D ⥤ C) := fun _ _ =>
  ⟨fun α β => NatTrans.ext (by subsingleton)⟩
def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    X ≅ Y where
  hom := f
  inv := g
instance subsingleton_iso {X Y : C} : Subsingleton (X ≅ Y) :=
  ⟨by
    intro i₁ i₂
    ext1
    subsingleton⟩
end CategoryTheory