import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.UniformSpace.Basic
open Uniformity Topology Filter UniformSpace Set
variable {γ : Type*}
def uniformSpaceOfCompactT2 [TopologicalSpace γ] [CompactSpace γ] [T2Space γ] : UniformSpace γ where
  uniformity := 𝓝ˢ (diagonal γ)
  symm := continuous_swap.tendsto_nhdsSet fun _ => Eq.symm
  comp := by
    set 𝓝Δ := 𝓝ˢ (diagonal γ)
    set F := 𝓝Δ.lift' fun s : Set (γ × γ) => s ○ s
    rw [le_iff_forall_inf_principal_compl]
    intro V V_in
    by_contra H
    haveI : NeBot (F ⊓ 𝓟 Vᶜ) := ⟨H⟩
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ p : γ × γ, ClusterPt p (F ⊓ 𝓟 Vᶜ) := exists_clusterPt_of_compactSpace _
    have clV : ClusterPt (x, y) (𝓟 <| Vᶜ) := hxy.of_inf_right
    have : (x, y) ∉ interior V := by
      have : (x, y) ∈ closure Vᶜ := by rwa [mem_closure_iff_clusterPt]
      rwa [closure_compl] at this
    have diag_subset : diagonal γ ⊆ interior V := subset_interior_iff_mem_nhdsSet.2 V_in
    have x_ne_y : x ≠ y := mt (@diag_subset (x, y)) this
    obtain
      ⟨U₁, _, V₁, V₁_in, U₂, _, V₂, V₂_in, V₁_cl, V₂_cl, U₁_op, U₂_op, VU₁, VU₂, hU₁₂⟩ :=
      disjoint_nested_nhds x_ne_y
    let U₃ := (V₁ ∪ V₂)ᶜ
    have U₃_op : IsOpen U₃ := (V₁_cl.union V₂_cl).isOpen_compl
    let W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃
    have W_in : W ∈ 𝓝Δ := by
      rw [mem_nhdsSet_iff_forall]
      rintro ⟨z, z'⟩ (rfl : z = z')
      refine IsOpen.mem_nhds ?_ ?_
      · apply_rules [IsOpen.union, IsOpen.prod]
      · simp only [W, mem_union, mem_prod, and_self_iff]
        exact (_root_.em _).imp_left fun h => union_subset_union VU₁ VU₂ h
    have : W ○ W ∈ F := @mem_lift' _ _ _ (fun s => s ○ s) _ W_in
    have hV₁₂ : V₁ ×ˢ V₂ ∈ 𝓝 (x, y) := prod_mem_nhds V₁_in V₂_in
    obtain ⟨⟨u, v⟩, ⟨u_in, v_in⟩, w, huw, hwv⟩ := clusterPt_iff.mp hxy.of_inf_left hV₁₂ this
    have uw_in : (u, w) ∈ U₁ ×ˢ U₁ :=
      (huw.resolve_right fun h => h.1 <| Or.inl u_in).resolve_right fun h =>
        hU₁₂.le_bot ⟨VU₁ u_in, h.1⟩
    have wv_in : (w, v) ∈ U₂ ×ˢ U₂ :=
      (hwv.resolve_right fun h => h.2 <| Or.inr v_in).resolve_left fun h =>
        hU₁₂.le_bot ⟨h.2, VU₂ v_in⟩
    exact hU₁₂.le_bot ⟨uw_in.2, wv_in.1⟩
  nhds_eq_comap_uniformity x := by
    simp_rw [nhdsSet_diagonal, comap_iSup, nhds_prod_eq, comap_prod, Function.comp_def, comap_id']
    rw [iSup_split_single _ x, comap_const_of_mem fun V => mem_of_mem_nhds]
    suffices ∀ y ≠ x, comap (fun _ : γ ↦ x) (𝓝 y) ⊓ 𝓝 y ≤ 𝓝 x by simpa
    intro y hxy
    simp [comap_const_of_not_mem (compl_singleton_mem_nhds hxy) (not_not_intro rfl)]