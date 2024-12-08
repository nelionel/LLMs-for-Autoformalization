import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.Quiver.Symmetric
namespace CategoryTheory
universe v v₂ u u₂
class Groupoid (obj : Type u) extends Category.{v} obj : Type max u (v + 1) where
  inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
  inv_comp : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by aesop_cat
  comp_inv : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by aesop_cat
initialize_simps_projections Groupoid (-Hom)
abbrev LargeGroupoid (C : Type (u + 1)) : Type (u + 1) :=
  Groupoid.{u} C
abbrev SmallGroupoid (C : Type u) : Type (u + 1) :=
  Groupoid.{u} C
section
variable {C : Type u} [Groupoid.{v} C] {X Y : C}
instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
  ⟨⟨Groupoid.inv f, Groupoid.comp_inv f, Groupoid.inv_comp f⟩⟩
@[simp]
theorem Groupoid.inv_eq_inv (f : X ⟶ Y) : Groupoid.inv f = CategoryTheory.inv f :=
  IsIso.eq_inv_of_hom_inv_id <| Groupoid.comp_inv f
@[simps]
def Groupoid.invEquiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
  ⟨Groupoid.inv, Groupoid.inv, fun f => by simp, fun f => by simp⟩
instance (priority := 100) groupoidHasInvolutiveReverse : Quiver.HasInvolutiveReverse C where
  reverse' f := Groupoid.inv f
  inv' f := by
    dsimp [Quiver.reverse]
    simp
@[simp]
theorem Groupoid.reverse_eq_inv (f : X ⟶ Y) : Quiver.reverse f = Groupoid.inv f :=
  rfl
instance functorMapReverse {D : Type*} [Groupoid D] (F : C ⥤ D) : F.toPrefunctor.MapReverse where
  map_reverse' f := by
    simp only [Quiver.reverse, Quiver.HasReverse.reverse', Groupoid.inv_eq_inv,
      Functor.map_inv]
variable (X Y)
def Groupoid.isoEquivHom : (X ≅ Y) ≃ (X ⟶ Y) where
  toFun := Iso.hom
  invFun f := ⟨f, Groupoid.inv f, (by aesop_cat), (by aesop_cat)⟩
  left_inv _ := Iso.ext rfl
  right_inv _ := rfl
variable (C)
@[simps]
noncomputable def Groupoid.invFunctor : C ⥤ Cᵒᵖ where
  obj := Opposite.op
  map {_ _} f := (inv f).op
end
section
variable {C : Type u} [Category.{v} C]
noncomputable def Groupoid.ofIsIso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), IsIso f) :
    Groupoid.{v} C where
  inv := fun f => CategoryTheory.inv f
  inv_comp := fun f => Classical.choose_spec (all_is_iso f).out|>.right
def Groupoid.ofHomUnique (all_unique : ∀ {X Y : C}, Unique (X ⟶ Y)) : Groupoid.{v} C where
  inv _ := all_unique.default
end
instance InducedCategory.groupoid {C : Type u} (D : Type u₂) [Groupoid.{v} D] (F : C → D) :
    Groupoid.{v} (InducedCategory D F) :=
  { InducedCategory.category F with
    inv := fun f => Groupoid.inv f
    inv_comp := fun f => Groupoid.inv_comp f
    comp_inv := fun f => Groupoid.comp_inv f }
section
instance groupoidPi {I : Type u} {J : I → Type u₂} [∀ i, Groupoid.{v} (J i)] :
    Groupoid.{max u v} (∀ i : I, J i) where
  inv f := fun i : I => Groupoid.inv (f i)
  comp_inv := fun f => by funext i; apply Groupoid.comp_inv
  inv_comp := fun f => by funext i; apply Groupoid.inv_comp
instance groupoidProd {α : Type u} {β : Type v} [Groupoid.{u₂} α] [Groupoid.{v₂} β] :
    Groupoid.{max u₂ v₂} (α × β) where
  inv f := (Groupoid.inv f.1, Groupoid.inv f.2)
end
end CategoryTheory