import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.UniformConvergence
open Filter Topology
open scoped Pointwise UniformConvergence Uniformity
section Module
variable (𝕜 α E H : Type*) {hom : Type*} [NormedField 𝕜] [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace H] [UniformSpace E] [UniformAddGroup E]
  [ContinuousSMul 𝕜 E] {𝔖 : Set <| Set α}
  [FunLike hom H (α → E)] [LinearMapClass hom 𝕜 H (α → E)]
lemma UniformFun.continuousSMul_induced_of_range_bounded (φ : hom)
    (hφ : IsInducing (ofFun ∘ φ)) (h : ∀ u : H, Bornology.IsVonNBounded 𝕜 (Set.range (φ u))) :
    ContinuousSMul 𝕜 H := by
  have : TopologicalAddGroup H :=
    let ofFun' : (α → E) →+ (α →ᵤ E) := AddMonoidHom.id _
    IsInducing.topologicalAddGroup (ofFun'.comp (φ : H →+ (α → E))) hφ
  have hb : (𝓝 (0 : H)).HasBasis (· ∈ 𝓝 (0 : E)) fun V ↦ {u | ∀ x, φ u x ∈ V} := by
    simp only [hφ.nhds_eq_comap, Function.comp_apply, map_zero]
    exact UniformFun.hasBasis_nhds_zero.comap _
  apply ContinuousSMul.of_basis_zero hb
  · intro U hU
    have : Tendsto (fun x : 𝕜 × E ↦ x.1 • x.2) (𝓝 0) (𝓝 0) :=
      continuous_smul.tendsto' _ _ (zero_smul _ _)
    rcases ((Filter.basis_sets _).prod_nhds (Filter.basis_sets _)).tendsto_left_iff.1 this U hU
      with ⟨⟨V, W⟩, ⟨hV, hW⟩, hVW⟩
    refine ⟨V, hV, W, hW, Set.smul_subset_iff.2 fun a ha u hu x ↦ ?_⟩
    rw [map_smul]
    exact hVW (Set.mk_mem_prod ha (hu x))
  · intro c U hU
    have : Tendsto (c • · : E → E) (𝓝 0) (𝓝 0) :=
      (continuous_const_smul c).tendsto' _ _ (smul_zero _)
    refine ⟨_, this hU, fun u hu x ↦ ?_⟩
    simpa only [map_smul] using hu x
  · intro u U hU
    simp only [Set.mem_setOf_eq, map_smul, Pi.smul_apply]
    simpa only [Set.mapsTo_range_iff] using (h u hU).eventually_nhds_zero (mem_of_mem_nhds hU)
lemma UniformOnFun.continuousSMul_induced_of_image_bounded (φ : hom) (hφ : IsInducing (ofFun 𝔖 ∘ φ))
    (h : ∀ u : H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 ((φ u : α → E) '' s)) :
    ContinuousSMul 𝕜 H := by
  obtain rfl := hφ.eq_induced; clear hφ
  simp only [induced_iInf, UniformOnFun.topologicalSpace_eq, induced_compose]
  refine continuousSMul_iInf fun s ↦ continuousSMul_iInf fun hs ↦ ?_
  letI : TopologicalSpace H :=
    .induced (UniformFun.ofFun ∘ s.restrict ∘ φ) (UniformFun.topologicalSpace s E)
  set φ' : H →ₗ[𝕜] (s → E) :=
    { toFun := s.restrict ∘ φ,
      map_smul' := fun c x ↦ by exact congr_arg s.restrict (map_smul φ c x),
      map_add' := fun x y ↦ by exact congr_arg s.restrict (map_add φ x y) }
  refine UniformFun.continuousSMul_induced_of_range_bounded 𝕜 s E H φ' ⟨rfl⟩ fun u ↦ ?_
  simpa only [Set.image_eq_range] using h u s hs
theorem UniformOnFun.continuousSMul_submodule_of_image_bounded (H : Submodule 𝕜 (α →ᵤ[𝔖] E))
    (h : ∀ u ∈ H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 (u '' s)) :
    @ContinuousSMul 𝕜 H _ _ ((UniformOnFun.topologicalSpace α E 𝔖).induced ((↑) : H → α →ᵤ[𝔖] E)) :=
  UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜 α E H
    (LinearMap.id.domRestrict H : H →ₗ[𝕜] α → E) IsInducing.subtypeVal fun ⟨u, hu⟩ => h u hu
end Module