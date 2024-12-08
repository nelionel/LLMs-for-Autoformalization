import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Properties
universe v u
open CategoryTheory Opposite TopologicalSpace Topology
namespace AlgebraicGeometry
@[mk_iff]
class IsClosedImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop where
  base_closed : IsClosedEmbedding f.base
  surj_on_stalks : ∀ x, Function.Surjective (f.stalkMap x)
lemma Scheme.Hom.isClosedEmbedding {X Y : Scheme} (f : X.Hom Y)
    [IsClosedImmersion f] : IsClosedEmbedding f.base :=
  IsClosedImmersion.base_closed
namespace IsClosedImmersion
@[deprecated (since := "2024-10-24")]
alias isClosedEmbedding := Scheme.Hom.isClosedEmbedding
@[deprecated (since := "2024-10-20")]
alias closedEmbedding := isClosedEmbedding
lemma eq_inf : @IsClosedImmersion = (topologically IsClosedEmbedding) ⊓
    stalkwise (fun f ↦ Function.Surjective f) := by
  ext X Y f
  rw [isClosedImmersion_iff]
  rfl
lemma iff_isPreimmersion {X Y : Scheme} {f : X ⟶ Y} :
    IsClosedImmersion f ↔ IsPreimmersion f ∧ IsClosed (Set.range f.base) := by
  rw [isClosedImmersion_iff, isPreimmersion_iff, ← surjectiveOnStalks_iff, and_comm, and_assoc,
    isClosedEmbedding_iff]
lemma of_isPreimmersion {X Y : Scheme} (f : X ⟶ Y) [IsPreimmersion f]
    (hf : IsClosed (Set.range f.base)) : IsClosedImmersion f :=
  iff_isPreimmersion.mpr ⟨‹_›, hf⟩
instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : IsPreimmersion f :=
  (iff_isPreimmersion.mp ‹_›).1
instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f where
  base_closed := Homeomorph.isClosedEmbedding <| TopCat.homeoOfIso (asIso f.base)
  surj_on_stalks := fun _ ↦ (ConcreteCategory.bijective_of_isIso _).2
instance : MorphismProperty.IsMultiplicative @IsClosedImmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨hg.base_closed.comp hf.base_closed, fun x ↦ ?_⟩
    rw [Scheme.stalkMap_comp]
    exact (hf.surj_on_stalks x).comp (hg.surj_on_stalks (f.base x))
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion f]
    [IsClosedImmersion g] : IsClosedImmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance
instance respectsIso : MorphismProperty.RespectsIso @IsClosedImmersion := by
  apply MorphismProperty.RespectsIso.mk <;> intro X Y Z e f hf <;> infer_instance
theorem spec_of_surjective {R S : CommRingCat} (f : R ⟶ S) (h : Function.Surjective f) :
    IsClosedImmersion (Spec.map f) where
  base_closed := PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ h
  surj_on_stalks x := by
    haveI : (RingHom.toMorphismProperty (fun f ↦ Function.Surjective f)).RespectsIso := by
      rw [← RingHom.toMorphismProperty_respectsIso_iff]
      exact RingHom.surjective_respectsIso
    apply (MorphismProperty.arrow_mk_iso_iff
      (RingHom.toMorphismProperty (fun f ↦ Function.Surjective f))
      (Scheme.arrowStalkMapSpecIso f x)).mpr
    exact RingHom.surjective_localRingHom_of_surjective f h x.asIdeal
instance spec_of_quotient_mk {R : CommRingCat.{u}} (I : Ideal R) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  spec_of_surjective _ Ideal.Quotient.mk_surjective
lemma of_surjective_of_isAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : Function.Surjective (f.appTop)) : IsClosedImmersion f := by
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (arrowIsoSpecΓOfIsAffine f)]
  apply spec_of_surjective
  exact h
theorem of_comp_isClosedImmersion {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion g]
    [IsClosedImmersion (f ≫ g)] : IsClosedImmersion f where
  base_closed := by
    have h := (f ≫ g).isClosedEmbedding
    simp only [Scheme.comp_coeBase, TopCat.coe_comp] at h
    refine .of_continuous_injective_isClosedMap (Scheme.Hom.continuous f) h.injective.of_comp ?_
    intro Z hZ
    rw [IsClosedEmbedding.isClosed_iff_image_isClosed g.isClosedEmbedding,
      ← Set.image_comp]
    exact h.isClosedMap _ hZ
  surj_on_stalks x := by
    have h := (f ≫ g).stalkMap_surjective x
    simp_rw [Scheme.stalkMap_comp] at h
    exact Function.Surjective.of_comp h
instance Spec_map_residue {X : Scheme.{u}} (x) : IsClosedImmersion (Spec.map (X.residue x)) :=
  IsClosedImmersion.spec_of_surjective (X.residue x)
    Ideal.Quotient.mk_surjective
instance {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : QuasiCompact f where
  isCompact_preimage _ _ hU' := base_closed.isCompact_preimage hU'
end IsClosedImmersion
section Affine
variable {X Y : Scheme.{u}} [IsAffine Y] {f : X ⟶ Y}
open IsClosedImmersion LocallyRingedSpace
lemma surjective_of_isClosed_range_of_injective [CompactSpace X]
    (hfcl : IsClosed (Set.range f.base)) (hfinj : Function.Injective (f.appTop)) :
    Function.Surjective f.base := by
  obtain ⟨I, hI⟩ := (Scheme.eq_zeroLocus_of_isClosed_of_isAffine Y (Set.range f.base)).mp hfcl
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  haveI (i : 𝒰.J) : IsAffine (𝒰.obj i) := Scheme.isAffine_affineCover X _
  apply Set.range_eq_univ.mp
  apply hI ▸ (Scheme.zeroLocus_eq_top_iff_subset_nilradical _).mpr
  intro s hs
  simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
    Submodule.mem_toAddSubmonoid, SetLike.mem_coe, mem_nilradical, ← IsNilpotent.map_iff hfinj]
  refine Scheme.isNilpotent_of_isNilpotent_cover _ 𝒰 (fun i ↦ ?_)
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
  rw [Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
  intro x
  suffices h : f.base ((𝒰.map i).base x.val) ∉ Y.basicOpen s by
    erw [← Scheme.Γevaluation_naturality_apply (𝒰.map i ≫ f)]
    simpa only [Scheme.comp_base, TopCat.coe_comp, Function.comp_apply,
      Scheme.residueFieldMap_comp, CommRingCat.comp_apply, map_eq_zero,
      Scheme.evaluation_eq_zero_iff_not_mem_basicOpen]
  exact (Y.mem_zeroLocus_iff I _).mp (hI ▸ Set.mem_range_self ((𝒰.map i).base x.val)) s hs
lemma stalkMap_injective_of_isOpenMap_of_injective [CompactSpace X]
    (hfopen : IsOpenMap f.base) (hfinj₁ : Function.Injective f.base)
    (hfinj₂ : Function.Injective (f.appTop)) (x : X) :
    Function.Injective (f.stalkMap x) := by
  let φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤) := f.appTop
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have (i : 𝒰.J) : IsAffine (𝒰.obj i) := Scheme.isAffine_affineCover X _
  let res (i : 𝒰.J) : Γ(X, ⊤) ⟶ Γ(𝒰.obj i, ⊤) := (𝒰.map i).appTop
  refine stalkMap_injective_of_isAffine _ _ (fun (g : Γ(Y, ⊤)) h ↦ ?_)
  rw [TopCat.Presheaf.Γgerm, Scheme.stalkMap_germ_apply] at h
  obtain ⟨U, w, (hx : x ∈ U), hg⟩ :=
    X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero ⊤ (φ g) ⟨x, trivial⟩ h
  obtain ⟨_, ⟨s, rfl⟩, hyv, bsle⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Y)
    (show f.base x ∈ ⟨f.base '' U.carrier, hfopen U.carrier U.is_open'⟩ from ⟨x, by simpa⟩)
  let W (i : 𝒰.J) : TopologicalSpace.Opens (𝒰.obj i) := (𝒰.obj i).basicOpen ((res i) (φ s))
  have hwle (i : 𝒰.J) : W i ≤ (𝒰.map i)⁻¹ᵁ U := by
    show (𝒰.obj i).basicOpen ((𝒰.map i ≫ f).appTop s) ≤ _
    rw [← Scheme.preimage_basicOpen_top, Scheme.comp_coeBase, Opens.map_comp_obj]
    refine Scheme.Hom.preimage_le_preimage_of_le _
      (le_trans (f.preimage_le_preimage_of_le bsle) (le_of_eq ?_))
    simp [Set.preimage_image_eq _ hfinj₁]
  have h0 (i : 𝒰.J) : (𝒰.map i).appLE _ (W i) (by simp) (φ g) = 0 := by
    rw [← Scheme.Hom.appLE_map _ _ (homOfLE <| hwle i).op, ← Scheme.Hom.map_appLE _ le_rfl w.op]
    simp only [CommRingCat.coe_comp_of, RingHom.coe_comp, Function.comp_apply]
    erw [hg]
    simp only [map_zero]
  have h1 (i : 𝒰.J) : ∃ n, (res i) (φ (s ^ n * g)) = 0 := by
    obtain ⟨n, hn⟩ := exists_of_res_zero_of_qcqs_of_top (s := ((res i) (φ s))) (h0 i)
    exact ⟨n, by rwa [map_mul, map_mul, map_pow, map_pow]⟩
  have h2 : ∃ n, ∀ i, (res i) (φ (s ^ n * g)) = 0 := by
    choose fn hfn using h1
    refine ⟨Finset.sup Finset.univ fn, fun i ↦ ?_⟩
    rw [map_mul, map_pow, map_mul, map_pow]
    simp only [map_mul, map_pow, map_mul, map_pow] at hfn
    apply pow_mul_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hfn i)
  obtain ⟨n, hn⟩ := h2
  apply germ_eq_zero_of_pow_mul_eq_zero (U := ⊤) ⟨f.base x, trivial⟩ hyv
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero] at hfinj₂
  exact hfinj₂ _ (Scheme.zero_of_zero_cover _ _ hn)
namespace IsClosedImmersion
theorem isIso_of_injective_of_isAffine [IsClosedImmersion f]
    (hf : Function.Injective (f.appTop)) : IsIso f := (isIso_iff_stalk_iso f).mpr <|
  have : CompactSpace X := f.isClosedEmbedding.compactSpace
  have hiso : IsIso f.base := TopCat.isIso_of_bijective_of_isClosedMap _
    ⟨f.isClosedEmbedding.injective,
     surjective_of_isClosed_range_of_injective f.isClosedEmbedding.isClosed_range hf⟩
    (f.isClosedEmbedding.isClosedMap)
  ⟨hiso, fun x ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨stalkMap_injective_of_isOpenMap_of_injective ((TopCat.homeoOfIso (asIso f.base)).isOpenMap)
    f.isClosedEmbedding.injective hf _, f.stalkMap_surjective x⟩⟩
variable (f)
theorem isAffine_surjective_of_isAffine [IsClosedImmersion f] :
    IsAffine X ∧ Function.Surjective (f.appTop) := by
  haveI i : IsClosedImmersion f := inferInstance
  rw [← affineTargetImageFactorization_comp f] at i ⊢
  haveI := of_surjective_of_isAffine (affineTargetImageInclusion f)
    (affineTargetImageInclusion_app_surjective f)
  haveI := IsClosedImmersion.of_comp_isClosedImmersion (affineTargetImageFactorization f)
    (affineTargetImageInclusion f)
  haveI := isIso_of_injective_of_isAffine (affineTargetImageFactorization_app_injective f)
  exact ⟨isAffine_of_isIso (affineTargetImageFactorization f),
    (ConcreteCategory.bijective_of_isIso
      ((affineTargetImageFactorization f).appTop)).surjective.comp <|
      affineTargetImageInclusion_app_surjective f⟩
end IsClosedImmersion
end Affine
instance IsClosedImmersion.isLocalAtTarget : IsLocalAtTarget @IsClosedImmersion :=
  eq_inf ▸ inferInstance
instance IsClosedImmersion.hasAffineProperty : HasAffineProperty @IsClosedImmersion
    (fun X _ f ↦ IsAffine X ∧ Function.Surjective (f.appTop)) := by
  convert HasAffineProperty.of_isLocalAtTarget @IsClosedImmersion
  refine ⟨fun ⟨h₁, h₂⟩ ↦ of_surjective_of_isAffine _ h₂, by apply isAffine_surjective_of_isAffine⟩
instance (priority := 900) {X Y : Scheme.{u}} (f : X ⟶ Y) [h : IsClosedImmersion f] :
    IsAffineHom f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsAffineHom) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsClosedImmersion (f ∣_ U) := IsLocalAtTarget.restrict h U
    exact this _ U.2
  rw [HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)]
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine f).1
instance IsClosedImmersion.isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsClosedImmersion := by
  apply HasAffineProperty.isStableUnderBaseChange
  haveI := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g ⟨ha, hsurj⟩
  exact ⟨inferInstance, RingHom.surjective_isStableUnderBaseChange.pullback_fst_appTop _
    RingHom.surjective_respectsIso f _ hsurj⟩
instance (priority := 900) {X Y : Scheme.{u}} (f : X ⟶ Y) [h : IsClosedImmersion f] :
    LocallyOfFiniteType f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsClosedImmersion (f ∣_ U) := IsLocalAtTarget.restrict h U
    exact this _ U.2
  obtain ⟨_, hf⟩ := h.isAffine_surjective_of_isAffine
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  exact RingHom.FiniteType.of_surjective (Scheme.Hom.app f ⊤) hf
lemma isIso_of_isClosedImmersion_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] [IsReduced Y] :
    IsIso f := by
  wlog hY : IsAffine Y
  · refine (IsLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme) Y.affineCover).mpr ?_
    intro i
    apply (config := { allowSynthFailures := true }) this
    · exact MorphismProperty.pullback_snd _ _ inferInstance
    · exact IsLocalAtTarget.of_isPullback (.of_hasPullback f (Y.affineCover.map i)) ‹_›
    · exact isReduced_of_isOpenImmersion (Y.affineCover.map i)
    · infer_instance
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  obtain ⟨hX, hf⟩ := HasAffineProperty.iff_of_isAffine.mp ‹IsClosedImmersion f›
  let φ := f.appTop
  suffices RingHom.ker φ ≤ nilradical _ by
    rwa [nilradical_eq_zero, Submodule.zero_eq_bot, le_bot_iff,
      ← RingHom.injective_iff_ker_eq_bot] at this
  refine (PrimeSpectrum.zeroLocus_eq_top_iff _).mp ?_
  rw [← range_specComap_of_surjective _ _ hf, Set.top_eq_univ, Set.range_eq_univ]
  have : Surjective (Spec.map (f.appTop)) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)).mp
    (inferInstanceAs (Surjective f))
  exact this.1
end AlgebraicGeometry