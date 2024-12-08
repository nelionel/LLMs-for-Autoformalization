import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.Data.TwoPointing
open CategoryTheory Option
universe u
variable {α β : Type*}
structure TwoP : Type (u + 1) where
  protected X : Type u
  toTwoPointing : TwoPointing X
namespace TwoP
instance : CoeSort TwoP Type* :=
  ⟨TwoP.X⟩
def of {X : Type*} (toTwoPointing : TwoPointing X) : TwoP :=
  ⟨X, toTwoPointing⟩
@[simp]
theorem coe_of {X : Type*} (toTwoPointing : TwoPointing X) : ↥(of toTwoPointing) = X :=
  rfl
alias _root_.TwoPointing.TwoP := of
instance : Inhabited TwoP :=
  ⟨of TwoPointing.bool⟩
noncomputable def toBipointed (X : TwoP) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed
@[simp]
theorem coe_toBipointed (X : TwoP) : ↥X.toBipointed = ↥X :=
  rfl
noncomputable instance largeCategory : LargeCategory TwoP :=
  InducedCategory.category toBipointed
noncomputable instance concreteCategory : ConcreteCategory TwoP :=
  InducedCategory.concreteCategory toBipointed
noncomputable instance hasForgetToBipointed : HasForget₂ TwoP Bipointed :=
  InducedCategory.hasForget₂ toBipointed
@[simps]
noncomputable def swap : TwoP ⥤ TwoP where
  obj X := ⟨X, X.toTwoPointing.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩
@[simps!]
noncomputable def swapEquiv : TwoP ≌ TwoP where
  functor := swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _
@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl
end TwoP
@[simp]
theorem TwoP_swap_comp_forget_to_Bipointed :
    TwoP.swap ⋙ forget₂ TwoP Bipointed = forget₂ TwoP Bipointed ⋙ Bipointed.swap :=
  rfl
@[simps]
noncomputable def pointedToTwoPFst : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm
@[simps]
noncomputable def pointedToTwoPSnd : Pointed.{u} ⥤ TwoP where
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm
@[simp]
theorem pointedToTwoPFst_comp_swap : pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd :=
  rfl
@[simp]
theorem pointedToTwoPSnd_comp_swap : pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst :=
  rfl
@[simp]
theorem pointedToTwoPFst_comp_forget_to_bipointed :
    pointedToTwoPFst ⋙ forget₂ TwoP Bipointed = pointedToBipointedFst :=
  rfl
@[simp]
theorem pointedToTwoPSnd_comp_forget_to_bipointed :
    pointedToTwoPSnd ⋙ forget₂ TwoP Bipointed = pointedToBipointedSnd :=
  rfl
noncomputable def pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwoPFst ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_snd.symm
            · rfl
          right_inv := fun _ => Pointed.Hom.ext rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }
noncomputable def pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwoPSnd ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_fst.symm
            · rfl
          right_inv := fun _ => Pointed.Hom.ext rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }