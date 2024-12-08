import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
universe v u
open CategoryTheory.Preadditive Opposite CategoryTheory.Limits
noncomputable section
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Preadditive C]
@[simps]
def preadditiveYonedaObj (Y : C) : Cᵒᵖ ⥤ ModuleCat.{v} (End Y) where
  obj X := ModuleCat.of _ (X.unop ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => f.unop ≫ g
      map_add' := fun _ _ => comp_add _ _ _ _ _ _
      map_smul' := fun _ _ => Eq.symm <| Category.assoc _ _ _ }
@[simps]
def preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrp.{v} where
  obj Y := preadditiveYonedaObj Y ⋙ forget₂ _ _
  map f :=
    { app := fun _ =>
        { toFun := fun g => g ≫ f
          map_zero' := Limits.zero_comp
          map_add' := fun _ _ => add_comp _ _ _ _ _ _ }
      naturality := fun _ _ _ => AddCommGrp.ext fun _ => Category.assoc _ _ _ }
  map_id _ := by ext; dsimp; simp
  map_comp f g := by ext; dsimp; simp
@[simps]
def preadditiveCoyonedaObj (X : Cᵒᵖ) : C ⥤ ModuleCat.{v} (End X) where
  obj Y := ModuleCat.of _ (unop X ⟶ Y)
  map f := ModuleCat.ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => add_comp _ _ _ _ _ _
      map_smul' := fun _ _ => Category.assoc _ _ _ }
@[simps]
def preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrp.{v} where
  obj X := preadditiveCoyonedaObj X ⋙ forget₂ _ _
  map f :=
    { app := fun _ =>
        { toFun := fun g => f.unop ≫ g
          map_zero' := Limits.comp_zero
          map_add' := fun _ _ => comp_add _ _ _ _ _ _ }
      naturality := fun _ _ _ =>
        AddCommGrp.ext fun _ => Eq.symm <| Category.assoc _ _ _ }
  map_id _ := by ext; dsimp; simp
  map_comp f g := by ext; dsimp; simp
attribute [nolint simpNF] CategoryTheory.preadditiveYoneda_map_app_apply
  CategoryTheory.preadditiveCoyoneda_map_app_apply
instance additive_yonedaObj (X : C) : Functor.Additive (preadditiveYonedaObj X) where
instance additive_yonedaObj' (X : C) : Functor.Additive (preadditiveYoneda.obj X) where
instance additive_coyonedaObj (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyonedaObj X) where
instance additive_coyonedaObj' (X : Cᵒᵖ) : Functor.Additive (preadditiveCoyoneda.obj X) where
@[simp]
theorem whiskering_preadditiveYoneda :
    preadditiveYoneda ⋙
        (whiskeringRight Cᵒᵖ AddCommGrp (Type v)).obj (forget AddCommGrp) =
      yoneda :=
  rfl
@[simp]
theorem whiskering_preadditiveCoyoneda :
    preadditiveCoyoneda ⋙
        (whiskeringRight C AddCommGrp (Type v)).obj (forget AddCommGrp) =
      coyoneda :=
  rfl
instance full_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrp).Full :=
  let _ : Functor.Full (preadditiveYoneda ⋙
      (whiskeringRight Cᵒᵖ AddCommGrp (Type v)).obj (forget AddCommGrp)) :=
    Yoneda.yoneda_full
  Functor.Full.of_comp_faithful preadditiveYoneda
    ((whiskeringRight Cᵒᵖ AddCommGrp (Type v)).obj (forget AddCommGrp))
instance full_preadditiveCoyoneda : (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrp).Full :=
  let _ : Functor.Full (preadditiveCoyoneda ⋙
      (whiskeringRight C AddCommGrp (Type v)).obj (forget AddCommGrp)) :=
    Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful preadditiveCoyoneda
    ((whiskeringRight C AddCommGrp (Type v)).obj (forget AddCommGrp))
instance faithful_preadditiveYoneda : (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrp).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveYoneda
instance faithful_preadditiveCoyoneda :
    (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrp).Faithful :=
  Functor.Faithful.of_comp_eq whiskering_preadditiveCoyoneda
end CategoryTheory