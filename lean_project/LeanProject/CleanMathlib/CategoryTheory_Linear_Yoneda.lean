import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
universe w v u
open Opposite
namespace CategoryTheory
variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable (C)
@[simps]
def linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R where
  obj X :=
    { obj := fun Y => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.leftComp R _ f.unop) }
  map {X₁ X₂} f :=
    { app := fun Y => @ModuleCat.ofHom R _ (Y.unop ⟶ X₁) (Y.unop ⟶ X₂) _ _ _ _
        (Linear.rightComp R _ f) }
@[simps]
def linearCoyoneda : Cᵒᵖ ⥤ C ⥤ ModuleCat R where
  obj Y :=
    { obj := fun X => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.rightComp R _ f) }
  map {Y₁ Y₂} f :=
    { app := fun X => @ModuleCat.ofHom R _ (unop Y₁ ⟶ X) (unop Y₂ ⟶ X) _ _ _ _
        (Linear.leftComp _ _ f.unop) }
instance linearYoneda_obj_additive (X : C) : ((linearYoneda R C).obj X).Additive where
instance linearCoyoneda_obj_additive (Y : Cᵒᵖ) : ((linearCoyoneda R C).obj Y).Additive where
@[simp]
theorem whiskering_linearYoneda :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = yoneda :=
  rfl
@[simp]
theorem whiskering_linearYoneda₂ :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGrp.{v}) =
      preadditiveYoneda :=
  rfl
@[simp]
theorem whiskering_linearCoyoneda :
    linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = coyoneda :=
  rfl
@[simp]
theorem whiskering_linearCoyoneda₂ :
    linearCoyoneda R C ⋙
        (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGrp.{v}) =
      preadditiveCoyoneda :=
  rfl
instance full_linearYoneda : (linearYoneda R C).Full :=
  let _ :  Functor.Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Yoneda.yoneda_full
  Functor.Full.of_comp_faithful (linearYoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))
instance full_linearCoyoneda : (linearCoyoneda R C).Full :=
  let _ : Functor.Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful (linearCoyoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))
instance faithful_linearYoneda : (linearYoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearYoneda R C)
instance faithful_linearCoyoneda : (linearCoyoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearCoyoneda R C)
end CategoryTheory