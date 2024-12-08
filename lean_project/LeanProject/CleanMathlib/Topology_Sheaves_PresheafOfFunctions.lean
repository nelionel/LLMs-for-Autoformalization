import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Sheaves.Presheaf
universe v u
open CategoryTheory
open TopologicalSpace
open Opposite
namespace TopCat
variable (X : TopCat.{v})
def presheafToTypes (T : X → Type v) : X.Presheaf (Type v) where
  obj U := ∀ x : U.unop, T x
  map {_ V} i g := fun x : V.unop => g (i.unop x)
  map_id U := by
    ext g
    rfl
  map_comp {_ _ _} _ _ := rfl
@[simp]
theorem presheafToTypes_obj {T : X → Type v} {U : (Opens X)ᵒᵖ} :
    (presheafToTypes X T).obj U = ∀ x : U.unop, T x :=
  rfl
@[simp]
theorem presheafToTypes_map {T : X → Type v} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToTypes X T).map i f = fun x => f (i.unop x) :=
  rfl
def presheafToType (T : Type v) : X.Presheaf (Type v) where
  obj U := U.unop → T
  map {_ _} i g := g ∘ i.unop
  map_id U := by
    ext g
    rfl
  map_comp {_ _ _} _ _ := rfl
@[simp]
theorem presheafToType_obj {T : Type v} {U : (Opens X)ᵒᵖ} :
    (presheafToType X T).obj U = (U.unop → T) :=
  rfl
@[simp]
theorem presheafToType_map {T : Type v} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToType X T).map i f = f ∘ i.unop :=
  rfl
def presheafToTop (T : TopCat.{v}) : X.Presheaf (Type v) :=
  (Opens.toTopCat X).op ⋙ yoneda.obj T
@[simp]
theorem presheafToTop_obj (T : TopCat.{v}) (U : (Opens X)ᵒᵖ) :
    (presheafToTop X T).obj U = ((Opens.toTopCat X).obj (unop U) ⟶ T) :=
  rfl
end TopCat