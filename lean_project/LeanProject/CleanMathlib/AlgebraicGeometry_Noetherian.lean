import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathlib.RingTheory.Localization.Submodule
universe u v
open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace
namespace AlgebraicGeometry
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : ∀ (U : X.affineOpens),
    IsNoetherianRing Γ(X, U) := by infer_instance
section localizationProps
variable {R : Type u} [CommRing R] (S : Finset R) (hS : Ideal.span (α := R) S = ⊤)
  (hN : ∀ s : S, IsNoetherianRing (Away (M := R) s))
include hS hN in
theorem isNoetherianRing_of_away : IsNoetherianRing R := by
  apply monotone_stabilizes_iff_noetherian.mp
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : ℕ | ∀ m : ℕ, n ≤ m → (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : ∀ s : S, minN s ∈ suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : ℕ →o Ideal (Away (M := R) s) :=
      ⟨fun n ↦ Ideal.map (floc s) (I n), fun _ _ h ↦ Ideal.map_mono (I.monotone h)⟩
    exact monotone_stabilizes_iff_noetherian.mpr (hN s) f
  let N := Finset.sup S minN
  use N
  have hN : ∀ s : S, minN s ≤ N := fun s => Finset.le_sup s.prop
  intro n hn
  rw [IsLocalization.ideal_eq_iInf_comap_map_away hS (I N),
      IsLocalization.ideal_eq_iInf_comap_map_away hS (I n),
      iInf_subtype', iInf_subtype']
  apply iInf_congr
  intro s
  congr 1
  rw [← hSuit s N (hN s)]
  exact hSuit s n <| Nat.le_trans (hN s) hn
end localizationProps
variable {X : Scheme}
theorem isLocallyNoetherian_of_affine_cover {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤)
    (hS' : ∀ i, IsNoetherianRing Γ(X, S i)) : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hN =>
    have := U.prop.isLocalization_basicOpen f
    exact IsLocalization.isNoetherianRing (.powers f) Γ(X, X.basicOpen f) hN
  | openCover U s _ hN =>
    apply isNoetherianRing_of_away s ‹_›
    intro ⟨f, hf⟩
    have : IsNoetherianRing Γ(X, X.basicOpen f) := hN ⟨f, hf⟩
    have := U.prop.isLocalization_basicOpen f
    have hEq := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
    exact isNoetherianRing_of_ringEquiv Γ(X, X.basicOpen f) hEq.symm.toRingEquiv
  | hU => exact hS' _
theorem isLocallyNoetherian_iff_of_iSup_eq_top {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsLocallyNoetherian X ↔ ∀ i, IsNoetherianRing Γ(X, S i) :=
  ⟨fun _ i => IsLocallyNoetherian.component_noetherian (S i),
   isLocallyNoetherian_of_affine_cover hS⟩
open CategoryTheory in
theorem isLocallyNoetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X)
    [∀ i, IsAffine (𝒰.obj i)] :
    IsLocallyNoetherian X ↔ ∀ (i : 𝒰.J), IsNoetherianRing Γ(𝒰.obj i, ⊤) := by
  constructor
  · intro h i
    let U := Scheme.Hom.opensRange (𝒰.map i)
    have := h.component_noetherian ⟨U, isAffineOpen_opensRange _⟩
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (IsOpenImmersion.ΓIsoTop (𝒰.map i)).symm
  · intro hCNoeth
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.map i), isAffineOpen_opensRange _⟩
    apply isLocallyNoetherian_of_affine_cover (S := fS)
    · rw [← Scheme.OpenCover.iSup_opensRange 𝒰]
    intro i
    apply isNoetherianRing_of_ringEquiv (R := Γ(𝒰.obj i, ⊤))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact IsOpenImmersion.ΓIsoTop (𝒰.map i)
lemma isLocallyNoetherian_of_isOpenImmersion {Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  let V : Y.affineOpens := ⟨f ''ᵁ U, IsAffineOpen.image_of_isOpenImmersion U.prop _⟩
  suffices Γ(X, U) ≅ Γ(Y, V) by
    convert isNoetherianRing_of_ringEquiv (R := Γ(Y, V)) _
    · apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
      exact this.symm
    · exact IsLocallyNoetherian.component_noetherian V
  rw [← Scheme.Hom.preimage_image_eq f U]
  trans
  · apply IsOpenImmersion.ΓIso
  · suffices Scheme.Hom.opensRange f ⊓ V = V by
      rw [this]
    rw [← Opens.coe_inj]
    rw [Opens.coe_inf, Scheme.Hom.opensRange_coe, IsOpenMap.functor_obj_coe,
      Set.inter_eq_right, Set.image_subset_iff, Set.preimage_range]
    exact Set.subset_univ _
theorem isLocallyNoetherian_iff_openCover (𝒰 : Scheme.OpenCover X) :
    IsLocallyNoetherian X ↔ ∀ (i : 𝒰.J), IsLocallyNoetherian (𝒰.obj i) := by
  constructor
  · intro h i
    exact isLocallyNoetherian_of_isOpenImmersion (𝒰.map i)
  · rw [isLocallyNoetherian_iff_of_affine_openCover (𝒰 := 𝒰.affineRefinement.openCover)]
    intro h i
    exact @isNoetherianRing_of_ringEquiv _ _ _ _
      (IsOpenImmersion.ΓIsoTop (Scheme.Cover.map _ i.2)).symm.commRingCatIsoToRingEquiv
      (IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange _⟩)
instance {R : CommRingCat} [IsNoetherianRing R] :
    NoetherianSpace (Spec R) := by
  convert PrimeSpectrum.instNoetherianSpace (R := R)
lemma noetherianSpace_of_isAffine [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] :
    NoetherianSpace X :=
  (noetherianSpace_iff_of_homeomorph X.isoSpec.inv.homeomorph).mp inferInstance
lemma noetherianSpace_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] :
    NoetherianSpace U := by
  have : IsNoetherianRing Γ(U, ⊤) := isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U)).symm.commRingCatIsoToRingEquiv
  exact @noetherianSpace_of_isAffine _ hU _
instance (priority := 100) {Z : Scheme} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [IsOpenImmersion f] : QuasiCompact f := by
  apply (quasiCompact_iff_forall_affine f).mpr
  intro U hU
  rw [Opens.map_coe, ← Set.preimage_inter_range]
  apply f.isOpenEmbedding.isInducing.isCompact_preimage'
  · apply (noetherianSpace_set_iff _).mp
    · convert noetherianSpace_of_isAffineOpen U hU
      apply IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    · exact Set.inter_subset_left
  · exact Set.inter_subset_right
instance (priority := 100) IsLocallyNoetherian.quasiSeparatedSpace [IsLocallyNoetherian X] :
    QuasiSeparatedSpace X := by
  apply (quasiSeparatedSpace_iff_affine X).mpr
  intro U V
  have hInd := U.2.fromSpec.isOpenEmbedding.isInducing
  apply (hInd.isCompact_preimage_iff ?_).mp
  · rw [← Set.preimage_inter_range, IsAffineOpen.range_fromSpec, Set.inter_comm]
    apply hInd.isCompact_preimage'
    · apply (noetherianSpace_set_iff _).mp
      · convert noetherianSpace_of_isAffineOpen U.1 U.2
        apply IsLocallyNoetherian.component_noetherian
      · exact Set.inter_subset_left
    · rw [IsAffineOpen.range_fromSpec]
      exact Set.inter_subset_left
  · rw [IsAffineOpen.range_fromSpec]
    exact Set.inter_subset_left
@[mk_iff]
class IsNoetherian (X : Scheme) extends IsLocallyNoetherian X, CompactSpace X : Prop
theorem isNoetherian_iff_of_finite_iSup_eq_top {ι} [Finite ι] {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsNoetherian X ↔ ∀ i, IsNoetherianRing Γ(X, S i) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_iSup_eq_top hS).mp
    exact h.toIsLocallyNoetherian
  · intro h
    convert IsNoetherian.mk
    · exact isLocallyNoetherian_of_affine_cover hS h
    · constructor
      rw [← Opens.coe_top, ← hS, Opens.iSup_mk]
      apply isCompact_iUnion
      intro i
      apply isCompact_iff_isCompact_univ.mpr
      convert CompactSpace.isCompact_univ
      have : NoetherianSpace (S i) := by
        apply noetherianSpace_of_isAffineOpen (S i).1 (S i).2
      apply NoetherianSpace.compactSpace (S i)
theorem isNoetherian_iff_of_finite_affine_openCover {𝒰 : Scheme.OpenCover.{v, u} X}
    [Finite 𝒰.J] [∀ i, IsAffine (𝒰.obj i)] :
    IsNoetherian X ↔ ∀ (i : 𝒰.J), IsNoetherianRing Γ(𝒰.obj i, ⊤) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_affine_openCover _).mp
    exact h.toIsLocallyNoetherian
  · intro hNoeth
    convert IsNoetherian.mk
    · exact (isLocallyNoetherian_iff_of_affine_openCover _).mpr hNoeth
    · exact Scheme.OpenCover.compactSpace 𝒰
open CategoryTheory in
instance (priority := 100) IsNoetherian.noetherianSpace [IsNoetherian X] :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  let 𝒰 := X.affineCover.finiteSubcover
  rw [← 𝒰.iUnion_range]
  suffices ∀ i : 𝒰.J, NoetherianSpace (Set.range <| (𝒰.map i).base) by
    apply NoetherianSpace.iUnion
  intro i
  have : IsAffine (𝒰.obj i) := by
    rw [X.affineCover.finiteSubcover_obj]
    apply Scheme.isAffine_affineCover
  let U : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.map i), isAffineOpen_opensRange _⟩
  convert noetherianSpace_of_isAffineOpen U.1 U.2
  apply IsLocallyNoetherian.component_noetherian
instance (priority := 100) quasiCompact_of_noetherianSpace_source {X Y : Scheme}
    [NoetherianSpace X] (f : X ⟶ Y) : QuasiCompact f :=
  ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
instance {R : CommRingCat} [IsNoetherianRing R] :
    IsLocallyNoetherian (Spec R) := by
  apply isLocallyNoetherian_of_affine_cover
    (ι := Fin 1) (S := fun _ => ⟨⊤, isAffineOpen_top (Spec R)⟩)
  · exact iSup_const
  · intro
    apply isNoetherianRing_of_ringEquiv R
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (Scheme.ΓSpecIso R).symm
instance (priority := 100) {R : CommRingCat}
    [IsLocallyNoetherian (Spec R)] : IsNoetherianRing R := by
  have := IsLocallyNoetherian.component_noetherian ⟨⊤, AlgebraicGeometry.isAffineOpen_top (Spec R)⟩
  apply isNoetherianRing_of_ringEquiv Γ(Spec R, ⊤)
  apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
  exact Scheme.ΓSpecIso R
instance {R : CommRingCat} [IsNoetherianRing R] :
    IsNoetherian (Spec R) where
instance {R} [CommRing R] [IsNoetherianRing R] :
    IsNoetherian (Spec (.of R)) := by
  suffices IsNoetherianRing (CommRingCat.of R) by infer_instance
  simp only [CommRingCat.coe_of]
  assumption
theorem isNoetherian_Spec {R : CommRingCat} :
    IsNoetherian (Spec R) ↔ IsNoetherianRing R :=
  ⟨fun _ => inferInstance,
   fun _ => inferInstance⟩
theorem finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
end AlgebraicGeometry