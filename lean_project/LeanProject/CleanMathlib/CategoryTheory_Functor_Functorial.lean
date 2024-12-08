import Mathlib.CategoryTheory.Functor.Basic
namespace CategoryTheory
universe v v₁ v₂ v₃ u u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  map' : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  map_id' : ∀ X : C, map' (𝟙 X) = 𝟙 (F X) := by aesop_cat
  map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map' (f ≫ g) = map' f ≫ map' g := by
    aesop_cat
def map (F : C → D) [Functorial.{v₁, v₂} F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
  Functorial.map'.{v₁, v₂} f
@[simp]
theorem map'_as_map {F : C → D} [Functorial.{v₁, v₂} F] {X Y : C} {f : X ⟶ Y} :
    Functorial.map'.{v₁, v₂} f = map F f :=
  rfl
@[simp]
theorem Functorial.map_id {F : C → D} [Functorial.{v₁, v₂} F] {X : C} : map F (𝟙 X) = 𝟙 (F X) :=
  Functorial.map_id' X
@[simp]
theorem Functorial.map_comp {F : C → D} [Functorial.{v₁, v₂} F] {X Y Z : C} {f : X ⟶ Y}
    {g : Y ⟶ Z} : map F (f ≫ g) = map F f ≫ map F g :=
  Functorial.map_comp' f g
namespace Functor
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F
           map := map F }
end Functor
instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with map' := F.map }
@[simp]
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl
instance functorial_id : Functorial.{v₁, v₁} (id : C → C) where map' f := f
section
variable {E : Type u₃} [Category.{v₃} E]
def functorial_comp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with map' := fun f => map G (map F f) }
end
end CategoryTheory