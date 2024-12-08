import Mathlib.CategoryTheory.Localization.LocalizerMorphism
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {E : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} E]
  {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
namespace Localization
def StrictUniversalPropertyFixedTarget.comp
    (h₁ : StrictUniversalPropertyFixedTarget L₁ W₁ E)
    (h₂ : StrictUniversalPropertyFixedTarget L₂ W₂ E)
    (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂))
    (hW₁₃ : W₁ ≤ W₃) (hW₂₃ : W₂ ≤ W₃.map L₁) :
    StrictUniversalPropertyFixedTarget (L₁ ⋙ L₂) W₃ E where
  inverts := hW₃
  lift F hF := h₂.lift (h₁.lift F (MorphismProperty.IsInvertedBy.of_le _ _  F hF hW₁₃)) (by
    refine MorphismProperty.IsInvertedBy.of_le _ _ _ ?_ hW₂₃
    simpa only [MorphismProperty.IsInvertedBy.map_iff, h₁.fac F] using hF)
  fac F hF := by rw [Functor.assoc, h₂.fac, h₁.fac]
  uniq _ _ h := h₂.uniq _ _ (h₁.uniq _ _ (by simpa only [Functor.assoc] using h))
end Localization
open Localization
namespace Functor
namespace IsLocalization
variable (L₁ W₁ L₂ W₂)
lemma comp [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂))
    (hW₁₃ : W₁ ≤ W₃) (hW₂₃ : W₂ ≤ W₃.map L₁) :
    (L₁ ⋙ L₂).IsLocalization W₃ := by
  let E₂ := Localization.uniq L₁ W₁.Q W₁
  let W₂' := W₂.map E₂.functor
  let Φ : LocalizerMorphism W₂ W₂' :=
    { functor := E₂.functor
      map := by
        have eq := W₂.isoClosure.inverseImage_map_eq_of_isEquivalence E₂.functor
        rw [MorphismProperty.map_isoClosure] at eq
        rw [eq]
        apply W₂.le_isoClosure }
  have := LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ (by rfl)
  let E₃ := (Φ.localizedFunctor L₂ W₂'.Q).asEquivalence
  let iso : (W₁.Q ⋙ W₂'.Q) ⋙ E₃.inverse ≅ L₁ ⋙ L₂ := by
    calc
      _ ≅ L₁ ⋙ E₂.functor ⋙ W₂'.Q ⋙ E₃.inverse :=
          Functor.associator _ _ _ ≪≫ isoWhiskerRight (compUniqFunctor L₁ W₁.Q W₁).symm _ ≪≫
            Functor.associator _ _ _
      _ ≅ L₁ ⋙ L₂ ⋙ E₃.functor ⋙ E₃.inverse :=
          isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
            isoWhiskerRight (Φ.catCommSq L₂ W₂'.Q).iso E₃.inverse ≪≫ Functor.associator _ _ _)
      _ ≅ L₁ ⋙ L₂ := isoWhiskerLeft _ (isoWhiskerLeft _ E₃.unitIso.symm ≪≫ L₂.rightUnitor)
  have hW₃' : W₃.IsInvertedBy (W₁.Q ⋙ W₂'.Q) := by
    simpa only [← MorphismProperty.IsInvertedBy.iff_comp _ _ E₃.inverse,
      MorphismProperty.IsInvertedBy.iff_of_iso W₃ iso] using hW₃
  have hW₂₃' : W₂' ≤ W₃.map W₁.Q := (MorphismProperty.monotone_map E₂.functor hW₂₃).trans
    (by simpa only [W₃.map_map]
      using le_of_eq (W₃.map_eq_of_iso (compUniqFunctor L₁ W₁.Q W₁)))
  have : (W₁.Q ⋙ W₂'.Q).IsLocalization W₃ := by
    refine IsLocalization.mk' _ _ ?_ ?_
    all_goals
      exact (StrictUniversalPropertyFixedTarget.comp
        (strictUniversalPropertyFixedTargetQ W₁ _)
        (strictUniversalPropertyFixedTargetQ W₂' _) W₃ hW₃' hW₁₃ hW₂₃')
  exact IsLocalization.of_equivalence_target _ W₃ _ E₃.symm iso
lemma of_comp (W₃ : MorphismProperty C₁)
    [L₁.IsLocalization W₁] [(L₁ ⋙ L₂).IsLocalization W₃]
    (hW₁₃ : W₁ ≤ W₃) (hW₂₃ : W₂ = W₃.map L₁) :
    L₂.IsLocalization W₂ := by
    have : (L₁ ⋙ W₂.Q).IsLocalization W₃ :=
      comp L₁ W₂.Q W₁ W₂ W₃ (fun X Y f hf => Localization.inverts W₂.Q W₂ _
        (by simpa only [hW₂₃] using W₃.map_mem_map _ _ hf)) hW₁₃
        (by rw [hW₂₃])
    exact IsLocalization.of_equivalence_target W₂.Q W₂ L₂
      (Localization.uniq (L₁ ⋙ W₂.Q) (L₁ ⋙ L₂) W₃)
      (liftNatIso L₁ W₁ _ _ _ _
        ((Functor.associator _ _ _).symm ≪≫
          Localization.compUniqFunctor (L₁ ⋙ W₂.Q) (L₁ ⋙ L₂) W₃))
end IsLocalization
end Functor
end CategoryTheory