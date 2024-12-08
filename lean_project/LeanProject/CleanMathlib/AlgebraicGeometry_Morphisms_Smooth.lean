import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.StandardSmooth
noncomputable section
open CategoryTheory
universe t w v u
namespace AlgebraicGeometry
open RingHom
variable (n m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
@[mk_iff]
class IsSmooth : Prop where
  exists_isStandardSmooth : ∀ (x : X), ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
    (e : V.1 ≤ f ⁻¹ᵁ U.1), IsStandardSmooth.{0, 0} (f.appLE U V e)
instance : HasRingHomProperty @IsSmooth (Locally IsStandardSmooth.{0, 0}) := by
  apply HasRingHomProperty.locally_of_iff
  · exact isStandardSmooth_localizationPreserves.away
  · exact isStandardSmooth_stableUnderCompositionWithLocalizationAway
  · intro X Y f
    rw [isSmooth_iff]
instance : MorphismProperty.IsStableUnderComposition @IsSmooth :=
  HasRingHomProperty.stableUnderComposition <| locally_stableUnderComposition
    isStandardSmooth_respectsIso isStandardSmooth_localizationPreserves
      isStandardSmooth_stableUnderComposition
instance isSmooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [IsSmooth f] [IsSmooth g] :
    IsSmooth (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹IsSmooth f› ‹IsSmooth g›
lemma isSmooth_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsSmooth :=
  HasRingHomProperty.isStableUnderBaseChange <| locally_isStableUnderBaseChange
    isStandardSmooth_respectsIso isStandardSmooth_isStableUnderBaseChange
@[mk_iff]
class IsSmoothOfRelativeDimension : Prop where
  exists_isStandardSmoothOfRelativeDimension : ∀ (x : X), ∃ (U : Y.affineOpens)
    (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
    IsStandardSmoothOfRelativeDimension.{0, 0} n (f.appLE U V e)
lemma IsSmoothOfRelativeDimension.isSmooth [IsSmoothOfRelativeDimension n f] : IsSmooth f where
  exists_isStandardSmooth x := by
    obtain ⟨U, V, hx, e, hf⟩ := exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
    exact ⟨U, V, hx, e, hf.isStandardSmooth⟩
instance : HasRingHomProperty (@IsSmoothOfRelativeDimension n)
    (Locally (IsStandardSmoothOfRelativeDimension.{0, 0} n)) := by
  apply HasRingHomProperty.locally_of_iff
  · exact (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
  · exact isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
  · intro X Y f
    rw [isSmoothOfRelativeDimension_iff]
lemma isSmoothOfRelativeDimension_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@IsSmoothOfRelativeDimension n) :=
  HasRingHomProperty.isStableUnderBaseChange <| locally_isStableUnderBaseChange
    isStandardSmoothOfRelativeDimension_respectsIso
    (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)
instance (priority := 900) [IsOpenImmersion f] : IsSmoothOfRelativeDimension 0 f :=
  HasRingHomProperty.of_isOpenImmersion
    (locally_holdsForLocalizationAway <|
      isStandardSmoothOfRelativeDimension_holdsForLocalizationAway).containsIdentities
instance (priority := 900) [IsOpenImmersion f] : IsSmooth f :=
  IsSmoothOfRelativeDimension.isSmooth 0 f
instance isSmoothOfRelativeDimension_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [hf : IsSmoothOfRelativeDimension n f] [hg : IsSmoothOfRelativeDimension m g] :
    IsSmoothOfRelativeDimension (n + m) (f ≫ g) where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨U₂, V₂, hfx₂, e₂, hf₂⟩ := hg.exists_isStandardSmoothOfRelativeDimension (f.base x)
    obtain ⟨U₁', V₁', hx₁', e₁', hf₁'⟩ := hf.exists_isStandardSmoothOfRelativeDimension x
    obtain ⟨r, s, hx₁, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      x V₂ U₁' V₁' V₁' hx₁' hx₁' e₁' hf₁' hfx₂
    have e : X.basicOpen s ≤ (f ≫ g) ⁻¹ᵁ U₂ :=
      le_trans e₁ <| f.preimage_le_preimage_of_le <| le_trans (Y.basicOpen_le r) e₂
    have heq : (f ≫ g).appLE U₂ (X.basicOpen s) e = g.appLE U₂ V₂ e₂ ≫
        algebraMap Γ(Y, V₂) Γ(Y, Y.basicOpen r) ≫ f.appLE (Y.basicOpen r) (X.basicOpen s) e₁ := by
      rw [RingHom.algebraMap_toAlgebra, g.appLE_map_assoc, Scheme.appLE_comp_appLE]
    refine ⟨U₂, ⟨X.basicOpen s, V₁'.2.basicOpen s⟩, hx₁, e, heq ▸ ?_⟩
    apply IsStandardSmoothOfRelativeDimension.comp ?_ hf₂
    haveI : IsLocalization.Away r Γ(Y, Y.basicOpen r) := V₂.2.isLocalization_basicOpen r
    exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁
instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsSmoothOfRelativeDimension 0 f]
    [IsSmoothOfRelativeDimension 0 g] :
    IsSmoothOfRelativeDimension 0 (f ≫ g) :=
  inferInstanceAs <| IsSmoothOfRelativeDimension (0 + 0) (f ≫ g)
instance : MorphismProperty.IsMultiplicative (@IsSmoothOfRelativeDimension 0) where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance
end AlgebraicGeometry