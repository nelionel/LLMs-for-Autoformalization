import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Types
universe v u
namespace CategoryTheory
section Category
variable {C : Type u} [Category.{v} C]
def IsIsomorphic : C → C → Prop := fun X Y => Nonempty (X ≅ Y)
variable (C)
def isIsomorphicSetoid : Setoid C where
  r := IsIsomorphic
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩
end Category
def isomorphismClasses : Cat.{v, u} ⥤ Type u where
  obj C := Quotient (isIsomorphicSetoid C.α)
  map {_ _} F := Quot.map F.obj fun _ _ ⟨f⟩ => ⟨F.mapIso f⟩
  map_id {C} := by  
    dsimp; apply funext; intro x
    apply @Quot.recOn _ _ _ x
    · intro _ _ p
      simp only [types_id_apply]
    · intro _
      rfl
  map_comp {C D E} f g := by 
    dsimp; apply funext; intro x
    apply @Quot.recOn _ _ _ x
    · intro _ _ _
      simp only [types_id_apply]
    · intro _
      rfl
theorem Groupoid.isIsomorphic_iff_nonempty_hom {C : Type u} [Groupoid.{v} C] {X Y : C} :
    IsIsomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  (Groupoid.isoEquivHom X Y).nonempty_congr
end CategoryTheory