import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
universe v u
open CategoryTheory TopologicalSpace Opposite MorphismProperty
namespace AlgebraicGeometry
section
variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
def affineAnd : AffineTargetMorphismProperty :=
  fun X _ f ↦ IsAffine X ∧ Q (f.appTop)
@[simp]
lemma affineAnd_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    affineAnd Q f ↔ IsAffine X ∧ Q (f.appTop) :=
  Iff.rfl
attribute [local simp] AffineTargetMorphismProperty.toProperty_apply
variable {Q}
lemma affineAnd_respectsIso (hP : RingHom.RespectsIso Q) :
    (affineAnd Q).toProperty.RespectsIso := by
  refine RespectsIso.mk _ ?_ ?_
  · intro X Y Z e f ⟨hZ, ⟨hY, hf⟩⟩
    simpa [hP.cancel_right_isIso, isAffine_of_isIso e.hom]
  · intro X Y Z e f ⟨hZ, hf⟩
    simpa [AffineTargetMorphismProperty.toProperty, isAffine_of_isIso e.inv, hP.cancel_left_isIso]
lemma affineAnd_isLocal (hPi : RingHom.RespectsIso Q) (hQl : RingHom.LocalizationPreserves Q)
    (hQs : RingHom.OfLocalizationSpan Q) : (affineAnd Q).IsLocal where
  respectsIso := affineAnd_respectsIso hPi
  to_basicOpen {X Y _} f r := fun ⟨hX, hf⟩ ↦ by
    simp only [Opens.map_top] at hf
    constructor
    · simp only [Scheme.preimage_basicOpen, Opens.map_top]
      exact (isAffineOpen_top X).basicOpen _
    · dsimp only
      rw [morphismRestrict_appTop, hPi.cancel_right_isIso, Scheme.Opens.ι_image_top]
      rw [(isAffineOpen_top Y).app_basicOpen_eq_away_map f (isAffineOpen_top X),
        hPi.cancel_right_isIso, ← Scheme.Hom.appTop]
      dsimp only [Opens.map_top]
      haveI := (isAffineOpen_top X).isLocalization_basicOpen (f.appTop r)
      apply hQl
      exact hf
  of_basicOpenCover {X Y _} f s hs hf := by
    dsimp [affineAnd] at hf
    haveI : IsAffine X := by
      apply isAffine_of_isAffineOpen_basicOpen (f.appTop '' s)
      · apply_fun Ideal.map (f.appTop) at hs
        rwa [Ideal.map_span, Ideal.map_top] at hs
      · rintro - ⟨r, hr, rfl⟩
        simp_rw [Scheme.preimage_basicOpen] at hf
        exact (hf ⟨r, hr⟩).left
    refine ⟨inferInstance, hQs.ofIsLocalization' hPi (f.appTop) s hs fun a ↦ ?_⟩
    refine ⟨Γ(Y, Y.basicOpen a.val), Γ(X, X.basicOpen (f.appTop a.val)), inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · exact (isAffineOpen_top X).isLocalization_basicOpen (f.appTop a.val)
    · obtain ⟨_, hf⟩ := hf a
      rw [morphismRestrict_appTop, hPi.cancel_right_isIso, Scheme.Opens.ι_image_top] at hf
      rw [(isAffineOpen_top Y).app_basicOpen_eq_away_map _ (isAffineOpen_top X)] at hf
      rwa [hPi.cancel_right_isIso] at hf
lemma affineAnd_isStableUnderBaseChange (hQi : RingHom.RespectsIso Q)
    (hQb : RingHom.IsStableUnderBaseChange Q) :
    (affineAnd Q).IsStableUnderBaseChange := by
  haveI : (affineAnd Q).toProperty.RespectsIso := affineAnd_respectsIso hQi
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g ⟨hY, hg⟩
  exact ⟨inferInstance, hQb.pullback_fst_appTop _ hQi f _ hg⟩
lemma targetAffineLocally_affineAnd_iff (hQi : RingHom.RespectsIso Q)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    targetAffineLocally (affineAnd Q) f ↔ ∀ U : Y.Opens, IsAffineOpen U →
      IsAffineOpen (f ⁻¹ᵁ U) ∧ Q (f.app U) := by
  simp only [targetAffineLocally, affineAnd_apply, morphismRestrict_app, hQi.cancel_right_isIso]
  refine ⟨fun hf U hU ↦ ?_, fun h U ↦ ?_⟩
  · obtain ⟨hfU, hf⟩ := hf ⟨U, hU⟩
    exact ⟨hfU, by rwa [Scheme.Opens.ι_image_top] at hf⟩
  · refine ⟨(h U U.2).1, ?_⟩
    rw [Scheme.Opens.ι_image_top]
    exact (h U U.2).2
lemma targetAffineLocally_affineAnd_iff' (hQi : RingHom.RespectsIso Q)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    targetAffineLocally (affineAnd Q) f ↔
      IsAffineHom f ∧ ∀ U : Y.Opens, IsAffineOpen U → Q (f.app U) := by
  rw [targetAffineLocally_affineAnd_iff hQi, isAffineHom_iff]
  aesop
lemma targetAffineLocally_affineAnd_iff_affineLocally (hQ : RingHom.PropertyIsLocal Q)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    targetAffineLocally (affineAnd Q) f ↔ IsAffineHom f ∧ affineLocally Q f := by
  haveI : HasRingHomProperty (affineLocally Q) Q := ⟨hQ, rfl⟩
  rw [targetAffineLocally_affineAnd_iff' hQ.respectsIso]
  simp only [and_congr_right_iff]
  intro hf
  constructor
  · wlog hY : IsAffine Y
    · intro h
      rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := affineLocally Q)
        _ (iSup_affineOpens_eq_top _)]
      intro U
      have : IsAffine (f ⁻¹ᵁ U) := hf.isAffine_preimage U U.2
      rw [HasRingHomProperty.iff_of_isAffine (P := affineLocally Q),
        morphismRestrict_appTop, hQ.respectsIso.cancel_right_isIso]
      apply h
      rw [Scheme.Opens.ι_image_top]
      exact U.2
    intro h
    have : IsAffine X := isAffine_of_isAffineHom f
    rw [HasRingHomProperty.iff_of_isAffine (P := affineLocally Q)]
    exact h ⊤ (isAffineOpen_top Y)
  · intro h U hU
    rw [affineLocally_iff_affineOpens_le] at h
    rw [f.app_eq_appLE]
    exact h ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hf.isAffine_preimage U hU⟩ (by simp)
lemma targetAffineLocally_affineAnd_eq_affineLocally (hQ : RingHom.PropertyIsLocal Q) :
    targetAffineLocally (affineAnd Q) =
      (@IsAffineHom ⊓ @affineLocally Q : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact targetAffineLocally_affineAnd_iff_affineLocally hQ f
variable {W : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
lemma targetAffineLocally_affineAnd_le
    (hQW : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, Q f → W f) :
    targetAffineLocally (affineAnd Q) ≤ targetAffineLocally (affineAnd W) := by
  intro X Y f h U
  exact ⟨(h U).1, hQW (h U).2⟩
end
section
variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
lemma HasAffineProperty.affineAnd_isStableUnderComposition {P : MorphismProperty Scheme.{u}}
    (hA : HasAffineProperty P (affineAnd Q)) (hQ : RingHom.StableUnderComposition Q) :
    P.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    haveI := hA
    wlog hZ : IsAffine Z
    · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this hA hQ _ _ (IsLocalAtTarget.restrict hf _) (IsLocalAtTarget.restrict hg _) hA U.2
    rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))] at hg
    obtain ⟨hY, hg⟩ := hg
    rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))] at hf
    obtain ⟨hX, hf⟩ := hf
    rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))]
    exact ⟨hX, hQ _ _ hg hf⟩
lemma HasAffineProperty.affineAnd_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    (_ : HasAffineProperty P (affineAnd Q)) (hQi : RingHom.RespectsIso Q)
    (hQb : RingHom.IsStableUnderBaseChange Q) :
    P.IsStableUnderBaseChange :=
  HasAffineProperty.isStableUnderBaseChange
    (AlgebraicGeometry.affineAnd_isStableUnderBaseChange hQi hQb)
lemma HasAffineProperty.affineAnd_containsIdentities {P : MorphismProperty Scheme.{u}}
    (hA : HasAffineProperty P (affineAnd Q)) (hQi : RingHom.RespectsIso Q)
    (hQ : RingHom.ContainsIdentities Q) :
    P.ContainsIdentities where
  id_mem X := by
    rw [eq_targetAffineLocally P, targetAffineLocally_affineAnd_iff hQi]
    intro U hU
    exact ⟨hU, hQ _⟩
lemma HasAffineProperty.affineAnd_iff (P : MorphismProperty Scheme.{u})
    (hQi : RingHom.RespectsIso Q) (hQl : RingHom.LocalizationPreserves Q)
    (hQs : RingHom.OfLocalizationSpan Q) :
    HasAffineProperty P (affineAnd Q) ↔
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ↔
        (IsAffineHom f ∧ ∀ U : Y.Opens, IsAffineOpen U → Q (f.app U)) := by
  simp_rw [isAffineHom_iff]
  refine ⟨fun h X Y f ↦ ?_, fun h ↦ ⟨affineAnd_isLocal hQi hQl hQs, ?_⟩⟩
  · rw [eq_targetAffineLocally P, targetAffineLocally_affineAnd_iff hQi]
    aesop
  · ext X Y f
    rw [targetAffineLocally_affineAnd_iff hQi, h f]
    aesop
lemma HasAffineProperty.affineAnd_le_isAffineHom (P : MorphismProperty Scheme.{u})
    (hA : HasAffineProperty P (affineAnd Q)) : P ≤ @IsAffineHom := by
  intro X Y f hf
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsAffineHom) _ (iSup_affineOpens_eq_top _)]
    intro U
    exact this P hA _ (IsLocalAtTarget.restrict hf _) U.2
  rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))] at hf
  rw [HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)]
  exact hf.1
lemma HasAffineProperty.affineAnd_eq_of_propertyIsLocal {P P' : MorphismProperty Scheme.{u}}
    (hP : HasAffineProperty P (affineAnd Q)) [HasRingHomProperty P' Q] :
    P = (@IsAffineHom ⊓ P' : MorphismProperty Scheme.{u}) := by
  rw [HasAffineProperty.eq_targetAffineLocally (P := P),
    targetAffineLocally_affineAnd_eq_affineLocally,
    HasRingHomProperty.eq_affineLocally (P := P')]
  exact HasRingHomProperty.isLocal_ringHomProperty P'
variable {Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
lemma HasAffineProperty.affineAnd_le_affineAnd {P P' : MorphismProperty Scheme.{u}}
    (hP : HasAffineProperty P (affineAnd Q)) (hP' : HasAffineProperty P' (affineAnd Q'))
    (hQQ' : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, Q f → Q' f) :
    P ≤ P' := by
  rw [HasAffineProperty.eq_targetAffineLocally (P := P),
    HasAffineProperty.eq_targetAffineLocally (P := P')]
  exact targetAffineLocally_affineAnd_le hQQ'
end
end AlgebraicGeometry