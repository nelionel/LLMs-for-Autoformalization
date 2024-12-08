import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.Equicontinuity
open Uniformity Topology Filter UniformSpace Set
variable {α β γ : Type*} [UniformSpace α] [UniformSpace β]
theorem CompactSpace.uniformContinuous_of_continuous [CompactSpace α] {f : α → β}
    (h : Continuous f) : UniformContinuous f :=
calc map (Prod.map f f) (𝓤 α)
   = map (Prod.map f f) (𝓝ˢ (diagonal α)) := by rw [nhdsSet_diagonal_eq_uniformity]
 _ ≤ 𝓝ˢ (diagonal β)                      := (h.prodMap h).tendsto_nhdsSet mapsTo_prod_map_diagonal
 _ ≤ 𝓤 β                                  := nhdsSet_diagonal_le_uniformity
theorem IsCompact.uniformContinuousOn_of_continuous {s : Set α} {f : α → β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_restrict] at hf
  exact CompactSpace.uniformContinuous_of_continuous hf
theorem IsCompact.uniformContinuousAt_of_continuousAt {r : Set (β × β)} {s : Set α}
    (hs : IsCompact s) (f : α → β) (hf : ∀ a ∈ s, ContinuousAt f a) (hr : r ∈ 𝓤 β) :
    { x : α × α | x.1 ∈ s → (f x.1, f x.2) ∈ r } ∈ 𝓤 α := by
  obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
  choose U hU T hT hb using fun a ha =>
    exists_mem_nhds_ball_subset_of_mem_nhds ((hf a ha).preimage_mem_nhds <| mem_nhds_left _ ht)
  obtain ⟨fs, hsU⟩ := hs.elim_nhds_subcover' U hU
  apply mem_of_superset ((biInter_finset_mem fs).2 fun a _ => hT a a.2)
  rintro ⟨a₁, a₂⟩ h h₁
  obtain ⟨a, ha, haU⟩ := Set.mem_iUnion₂.1 (hsU h₁)
  apply htr
  refine ⟨f a, htsymm.mk_mem_comm.1 (hb _ _ _ haU ?_), hb _ _ _ haU ?_⟩
  exacts [mem_ball_self _ (hT a a.2), mem_iInter₂.1 h a ha]
theorem Continuous.uniformContinuous_of_tendsto_cocompact {f : α → β} {x : β}
    (h_cont : Continuous f) (hx : Tendsto f (cocompact α) (𝓝 x)) : UniformContinuous f :=
  uniformContinuous_def.2 fun r hr => by
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    obtain ⟨s, hs, hst⟩ := mem_cocompact.1 (hx <| mem_nhds_left _ ht)
    apply
      mem_of_superset
        (symmetrize_mem_uniformity <|
          (hs.uniformContinuousAt_of_continuousAt f fun _ _ => h_cont.continuousAt) <|
            symmetrize_mem_uniformity hr)
    rintro ⟨b₁, b₂⟩ h
    by_cases h₁ : b₁ ∈ s; · exact (h.1 h₁).1
    by_cases h₂ : b₂ ∈ s; · exact (h.2 h₂).2
    apply htr
    exact ⟨x, htsymm.mk_mem_comm.1 (hst h₁), hst h₂⟩
@[to_additive]
theorem HasCompactMulSupport.uniformContinuous_of_continuous {f : α → β} [One β]
    (h1 : HasCompactMulSupport f) (h2 : Continuous f) : UniformContinuous f :=
  h2.uniformContinuous_of_tendsto_cocompact h1.is_one_at_infty
theorem ContinuousOn.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    {f : α → β → γ} {x : α} {U : Set α} (hxU : U ∈ 𝓝 x) (h : ContinuousOn (↿f) (U ×ˢ univ)) :
    TendstoUniformly f (f x) (𝓝 x) := by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn (↿f) (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ)
      (h.mono <| prod_mono hKU Subset.rfl)
  exact this.tendstoUniformly hxK
theorem Continuous.tendstoUniformly [WeaklyLocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    (f : α → β → γ) (h : Continuous ↿f) (x : α) : TendstoUniformly f (f x) (𝓝 x) :=
  let ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have : UniformContinuousOn (↿f) (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ) h.continuousOn
  this.tendstoUniformly hxK
lemma IsCompact.mem_uniformity_of_prod
    {α β E : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace E]
    {f : α → β → E} {s : Set α} {k : Set β} {q : α} {u : Set (E × E)}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ k)) (hq : q ∈ s) (hu : u ∈ 𝓤 E) :
    ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ k, (f p x, f q x) ∈ u := by
  apply hk.induction_on (p := fun t ↦ ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ t, (f p x, f q x) ∈ u)
  · exact ⟨univ, univ_mem, by simp⟩
  · intro t' t ht't ⟨v, v_mem, hv⟩
    exact ⟨v, v_mem, fun p hp x hx ↦ hv p hp x (ht't hx)⟩
  · intro t t' ⟨v, v_mem, hv⟩ ⟨v', v'_mem, hv'⟩
    refine ⟨v ∩ v', inter_mem v_mem v'_mem, fun p hp x hx ↦ ?_⟩
    rcases hx with h'x|h'x
    · exact hv p hp.1 x h'x
    · exact hv' p hp.2 x h'x
  · rcases comp_symm_of_uniformity hu with ⟨u', u'_mem, u'_symm, hu'⟩
    intro x hx
    obtain ⟨v, hv, w, hw, hvw⟩ :
      ∃ v ∈ 𝓝[s] q, ∃ w ∈ 𝓝[k] x, v ×ˢ w ⊆ f.uncurry ⁻¹' {z | (f q x, z) ∈ u'} :=
        mem_nhdsWithin_prod_iff.1 (hf (q, x) ⟨hq, hx⟩ (mem_nhds_left (f q x) u'_mem))
    refine ⟨w, hw, v, hv, fun p hp y hy ↦ ?_⟩
    have A : (f q x, f p y) ∈ u' := hvw (⟨hp, hy⟩ : (p, y) ∈ v ×ˢ w)
    have B : (f q x, f q y) ∈ u' := hvw (⟨mem_of_mem_nhdsWithin hq hv, hy⟩ : (q, y) ∈ v ×ˢ w)
    exact hu' (prod_mk_mem_compRel (u'_symm A) B)
section UniformConvergence
theorem CompactSpace.uniformEquicontinuous_of_equicontinuous {ι : Type*} {F : ι → β → α}
    [CompactSpace β] (h : Equicontinuous F) : UniformEquicontinuous F := by
  rw [equicontinuous_iff_continuous] at h
  rw [uniformEquicontinuous_iff_uniformContinuous]
  exact CompactSpace.uniformContinuous_of_continuous h
end UniformConvergence