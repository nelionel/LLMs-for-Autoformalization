import Mathlib.CategoryTheory.Monoidal.Category
universe v u
open CategoryTheory MonoidalCategory
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]
open scoped MonoidalCategory
class MonoidalCoherence (X Y : C) where
  iso : X ≅ Y
scoped[CategoryTheory.MonoidalCategory] notation " ⊗𝟙 " =>
  MonoidalCoherence.iso 
abbrev monoidalIso (X Y : C) [MonoidalCoherence X Y] : X ≅ Y := MonoidalCoherence.iso
def monoidalComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ ⊗𝟙.hom ≫ g
@[inherit_doc monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ⊗≫ " =>
  monoidalComp 
def monoidalIsoComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ ⊗𝟙 ≪≫ g
@[inherit_doc monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪⊗≫ " =>
  monoidalIsoComp 
namespace MonoidalCoherence
variable [MonoidalCategory C]
@[simps]
instance refl (X : C) : MonoidalCoherence X X := ⟨Iso.refl _⟩
@[simps]
instance whiskerLeft (X Y Z : C) [MonoidalCoherence Y Z] :
    MonoidalCoherence (X ⊗ Y) (X ⊗ Z) :=
  ⟨whiskerLeftIso X ⊗𝟙⟩
@[simps]
instance whiskerRight (X Y Z : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ Z) (Y ⊗ Z) :=
  ⟨whiskerRightIso ⊗𝟙 Z⟩
@[simps]
instance tensor_right (X Y : C) [MonoidalCoherence (𝟙_ C) Y] :
    MonoidalCoherence X (X ⊗ Y) :=
  ⟨(ρ_ X).symm ≪≫ (whiskerLeftIso X ⊗𝟙)⟩
@[simps]
instance tensor_right' (X Y : C) [MonoidalCoherence Y (𝟙_ C)] :
    MonoidalCoherence (X ⊗ Y) X :=
  ⟨whiskerLeftIso X ⊗𝟙 ≪≫ (ρ_ X)⟩
@[simps]
instance left (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (𝟙_ C ⊗ X) Y :=
  ⟨λ_ X ≪≫ ⊗𝟙⟩
@[simps]
instance left' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (𝟙_ C ⊗ Y) :=
  ⟨⊗𝟙 ≪≫ (λ_ Y).symm⟩
@[simps]
instance right (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ 𝟙_ C) Y :=
  ⟨ρ_ X ≪≫ ⊗𝟙⟩
@[simps]
instance right' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (Y ⊗ 𝟙_ C) :=
  ⟨⊗𝟙 ≪≫ (ρ_ Y).symm⟩
@[simps]
instance assoc (X Y Z W : C) [MonoidalCoherence (X ⊗ (Y ⊗ Z)) W] :
    MonoidalCoherence ((X ⊗ Y) ⊗ Z) W :=
  ⟨α_ X Y Z ≪≫ ⊗𝟙⟩
@[simps]
instance assoc' (W X Y Z : C) [MonoidalCoherence W (X ⊗ (Y ⊗ Z))] :
    MonoidalCoherence W ((X ⊗ Y) ⊗ Z) :=
  ⟨⊗𝟙 ≪≫ (α_ X Y Z).symm⟩
end MonoidalCoherence
@[simp] lemma monoidalComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗≫ g = f ≫ g := by
  simp [monoidalComp]
end CategoryTheory