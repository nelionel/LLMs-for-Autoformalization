import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Monoidal.Category
namespace CategoryTheory
variable {C : Type*} [Bicategory C]
def EndMonoidal (X : C) :=
  X ⟶ X 
instance (X : C) : Category (EndMonoidal X) :=
  show Category (X ⟶ X) from inferInstance
instance (X : C) : Inhabited (EndMonoidal X) :=
  ⟨𝟙 X⟩
open Bicategory
open MonoidalCategory
open Bicategory
attribute [local simp] EndMonoidal in
instance (X : C) : MonoidalCategory (EndMonoidal X) where
  tensorObj f g := f ≫ g
  whiskerLeft {f _ _} η := f ◁ η
  whiskerRight {_ _} η h := η ▷ h
  tensorUnit := 𝟙 _
  associator f g h := α_ f g h
  leftUnitor f := λ_ f
  rightUnitor f := ρ_ f
  tensor_comp := by
    intros
    dsimp
    rw [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight, Category.assoc, Category.assoc,
      Bicategory.whisker_exchange_assoc]
end CategoryTheory