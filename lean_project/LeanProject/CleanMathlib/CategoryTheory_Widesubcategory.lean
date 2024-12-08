import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.MorphismProperty.Composition
namespace CategoryTheory
universe v₁ v₂ u₁ u₂
open MorphismProperty
section Induced
variable {C : Type u₁} (D : Type u₂) [Category.{v₁} D]
variable (F : C → D) (P : MorphismProperty D) [P.IsMultiplicative]
@[nolint unusedArguments]
def InducedWideCategory (_F : C → D) (_P : MorphismProperty D) [IsMultiplicative _P] :=
  C
variable {D}
instance InducedWideCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedWideCategory D F P) α :=
  ⟨fun c => F c⟩
@[simps!]
instance InducedWideCategory.category :
    Category (InducedWideCategory D F P) where
  Hom X Y := {f : F X ⟶ F Y | P f}
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {_ _ _} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩
@[simps]
def wideInducedFunctor : InducedWideCategory D F P ⥤ D where
  obj := F
  map {_ _} f := f.1
instance InducedWideCategory.faithful : (wideInducedFunctor F P).Faithful where
  map_injective {X Y} f g eq := by
    cases f
    cases g
    aesop
end Induced
section WideSubcategory
variable {C : Type u₁} [Category.{v₁} C]
variable (P : MorphismProperty C) [IsMultiplicative P]
@[ext, nolint unusedArguments]
structure WideSubcategory (_P : MorphismProperty C) [IsMultiplicative _P] where
  obj : C
instance WideSubcategory.category : Category.{v₁} (WideSubcategory P) :=
  InducedWideCategory.category WideSubcategory.obj P
@[simp]
lemma WideSubcategory.id_def (X : WideSubcategory P) : (CategoryStruct.id X).1 = 𝟙 X.obj := rfl
@[simp]
lemma WideSubcategory.comp_def {X Y Z : WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = (f.1 ≫ g.1 : X.obj ⟶ Z.obj) := rfl
def wideSubcategoryInclusion : WideSubcategory P ⥤ C :=
  wideInducedFunctor WideSubcategory.obj P
@[simp]
theorem wideSubcategoryInclusion.obj (X) : (wideSubcategoryInclusion P).obj X = X.obj :=
  rfl
@[simp]
theorem wideSubcategoryInclusion.map {X Y} {f : X ⟶ Y} :
    (wideSubcategoryInclusion P).map f = f.1 :=
  rfl
instance wideSubcategory.faithful : (wideSubcategoryInclusion P).Faithful :=
  inferInstanceAs (wideInducedFunctor WideSubcategory.obj P).Faithful
end WideSubcategory
end CategoryTheory