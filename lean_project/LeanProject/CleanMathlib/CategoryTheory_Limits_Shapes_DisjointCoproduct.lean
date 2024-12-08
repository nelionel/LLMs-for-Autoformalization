import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
universe v u u₂
namespace CategoryTheory
namespace Limits
open Category
variable {C : Type u} [Category.{v} C]
class CoproductDisjoint (X₁ X₂ : C) where
  isInitialOfIsPullbackOfIsCoproduct :
    ∀ {X Z} {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} {f : Z ⟶ X₁} {g : Z ⟶ X₂}
      (_cX : IsColimit (BinaryCofan.mk pX₁ pX₂)) {comm : f ≫ pX₁ = g ≫ pX₂},
      IsLimit (PullbackCone.mk _ _ comm) → IsInitial Z
  mono_inl : ∀ (X) (X₁ : X₁ ⟶ X) (X₂ : X₂ ⟶ X) (_cX : IsColimit (BinaryCofan.mk X₁ X₂)), Mono X₁
  mono_inr : ∀ (X) (X₁ : X₁ ⟶ X) (X₂ : X₂ ⟶ X) (_cX : IsColimit (BinaryCofan.mk X₁ X₂)), Mono X₂
def isInitialOfIsPullbackOfIsCoproduct {Z X₁ X₂ X : C} [CoproductDisjoint X₁ X₂] {pX₁ : X₁ ⟶ X}
    {pX₂ : X₂ ⟶ X} (cX : IsColimit (BinaryCofan.mk pX₁ pX₂)) {f : Z ⟶ X₁} {g : Z ⟶ X₂}
    {comm : f ≫ pX₁ = g ≫ pX₂} (cZ : IsLimit (PullbackCone.mk _ _ comm)) : IsInitial Z :=
  CoproductDisjoint.isInitialOfIsPullbackOfIsCoproduct cX cZ
noncomputable def isInitialOfIsPullbackOfCoproduct {Z X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂]
    [CoproductDisjoint X₁ X₂] {f : Z ⟶ X₁} {g : Z ⟶ X₂}
    {comm : f ≫ (coprod.inl : X₁ ⟶ _ ⨿ X₂) = g ≫ coprod.inr}
    (cZ : IsLimit (PullbackCone.mk _ _ comm)) : IsInitial Z :=
  CoproductDisjoint.isInitialOfIsPullbackOfIsCoproduct (coprodIsCoprod _ _) cZ
noncomputable def isInitialOfPullbackOfIsCoproduct {X X₁ X₂ : C} [CoproductDisjoint X₁ X₂]
    {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} [HasPullback pX₁ pX₂] (cX : IsColimit (BinaryCofan.mk pX₁ pX₂)) :
    IsInitial (pullback pX₁ pX₂) :=
  CoproductDisjoint.isInitialOfIsPullbackOfIsCoproduct cX (pullbackIsPullback _ _)
noncomputable def isInitialOfPullbackOfCoproduct {X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂]
    [CoproductDisjoint X₁ X₂] [HasPullback (coprod.inl : X₁ ⟶ _ ⨿ X₂) coprod.inr] :
    IsInitial (pullback (coprod.inl : X₁ ⟶ _ ⨿ X₂) coprod.inr) :=
  isInitialOfIsPullbackOfCoproduct (pullbackIsPullback _ _)
instance {X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂] [CoproductDisjoint X₁ X₂] :
    Mono (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) :=
  CoproductDisjoint.mono_inl _ _ _ (coprodIsCoprod _ _)
instance {X₁ X₂ : C} [HasBinaryCoproduct X₁ X₂] [CoproductDisjoint X₁ X₂] :
    Mono (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) :=
  CoproductDisjoint.mono_inr _ _ _ (coprodIsCoprod _ _)
class CoproductsDisjoint (C : Type u) [Category.{v} C] where
  CoproductDisjoint : ∀ X Y : C, CoproductDisjoint X Y
attribute [instance 999] CoproductsDisjoint.CoproductDisjoint
theorem initialMonoClass_of_disjoint_coproducts [CoproductsDisjoint C] : InitialMonoClass C where
  isInitial_mono_from X hI :=
    CoproductDisjoint.mono_inl X (IsInitial.to hI X) (CategoryTheory.CategoryStruct.id X)
      { desc := fun s : BinaryCofan _ _ => s.inr
        fac := fun _s j =>
          Discrete.casesOn j fun j => WalkingPair.casesOn j (hI.hom_ext _ _) (id_comp _)
        uniq := fun (_s : BinaryCofan _ _) _m w =>
          (id_comp _).symm.trans (w ⟨WalkingPair.right⟩) }
end Limits
end CategoryTheory