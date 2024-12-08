import Mathlib.Control.EquivFunctor
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Types
namespace CategoryTheory
universe v₁ v₂ u₁ u₂
def Core (C : Type u₁) := C
variable {C : Type u₁} [Category.{v₁} C]
instance coreCategory : Groupoid.{v₁} (Core C) where
  Hom (X Y : C) := X ≅ Y
  id (X : C) := Iso.refl X
  comp f g := Iso.trans f g
  inv {_ _} f := Iso.symm f
namespace Core
@[simp]
theorem id_hom (X : C) : Iso.hom (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl
@[simp]
theorem comp_hom {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl
variable (C)
def inclusion : Core C ⥤ C where
  obj := id
  map f := f.hom
instance : (inclusion C).Faithful where
  map_injective := by
    intro _ _
    apply Iso.ext
variable {C} {G : Type u₂} [Groupoid.{v₂} G]
def functorToCore (F : G ⥤ C) : G ⥤ Core C where
  obj X := F.obj X
  map f := { hom := F.map f, inv := F.map (Groupoid.inv f) }
def forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C :=
  (whiskeringRight _ _ _).obj (inclusion C)
end Core
def ofEquivFunctor (m : Type u₁ → Type u₂) [EquivFunctor m] : Core (Type u₁) ⥤ Core (Type u₂) where
  obj := m
  map f := (EquivFunctor.mapEquiv m f.toEquiv).toIso
  map_id α := by apply Iso.ext; funext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    apply Iso.ext; funext x; dsimp
    erw [Iso.toEquiv_comp, EquivFunctor.map_trans']
    rw [Function.comp]
end CategoryTheory