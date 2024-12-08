import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Filter
assert_not_exists StoneCech
open Filter Topology Function Set
open Prod (fst snd)
variable {X Y Z W ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W] {f : X → Y} {g : Y → Z}
universe u v
@[mk_iff isProperMap_iff_clusterPt, fun_prop]
structure IsProperMap (f : X → Y) extends Continuous f : Prop where
  clusterPt_of_mapClusterPt :
    ∀ ⦃ℱ : Filter X⦄, ∀ ⦃y : Y⦄, MapClusterPt y ℱ f → ∃ x, f x = y ∧ ClusterPt x ℱ
add_decl_doc isProperMap_iff_clusterPt
@[fun_prop]
lemma IsProperMap.continuous (h : IsProperMap f) : Continuous f := h.toContinuous
lemma IsProperMap.isClosedMap (h : IsProperMap f) : IsClosedMap f := by
  rw [isClosedMap_iff_clusterPt]
  exact fun s y ↦ h.clusterPt_of_mapClusterPt (ℱ := 𝓟 s) (y := y)
lemma isProperMap_iff_ultrafilter : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃𝒰 : Ultrafilter X⦄, ∀ ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) → ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x := by
  rw [isProperMap_iff_clusterPt]
  refine and_congr_right (fun _ ↦ ?_)
  constructor <;> intro H
  · intro 𝒰 y (hY : (Ultrafilter.map f 𝒰 : Filter Y) ≤ _)
    simp_rw [← Ultrafilter.clusterPt_iff] at hY ⊢
    exact H hY
  · simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, ← exists_ultrafilter_iff,
      forall_exists_index]
    intro ℱ y 𝒰 hy
    rcases H (tendsto_iff_comap.mpr <| hy.trans inf_le_left) with ⟨x, hxy, hx⟩
    exact ⟨x, hxy, 𝒰, le_inf hx (hy.trans inf_le_right)⟩
lemma isProperMap_iff_ultrafilter_of_t2 [T2Space Y] : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃𝒰 : Ultrafilter X⦄, ∀ ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) → ∃ x, 𝒰.1 ≤ 𝓝 x :=
  isProperMap_iff_ultrafilter.trans <| and_congr_right fun hc ↦ forall₃_congr fun _𝒰 _y hy ↦
    exists_congr fun x ↦ and_iff_right_of_imp fun h ↦
      tendsto_nhds_unique ((hc.tendsto x).mono_left h) hy
lemma IsProperMap.ultrafilter_le_nhds_of_tendsto (h : IsProperMap f) ⦃𝒰 : Ultrafilter X⦄ ⦃y : Y⦄
    (hy : Tendsto f 𝒰 (𝓝 y)) : ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x :=
  (isProperMap_iff_ultrafilter.mp h).2 hy
lemma IsProperMap.comp (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) := by
  refine ⟨by fun_prop, fun ℱ z h ↦ ?_⟩
  rw [mapClusterPt_comp] at h
  rcases hg.clusterPt_of_mapClusterPt h with ⟨y, rfl, hy⟩
  rcases hf.clusterPt_of_mapClusterPt hy with ⟨x, rfl, hx⟩
  use x, rfl
lemma isProperMap_of_comp_of_surj (hf : Continuous f)
    (hg : Continuous g) (hgf : IsProperMap (g ∘ f)) (f_surj : f.Surjective) : IsProperMap g := by
  refine ⟨hg, fun ℱ z h ↦ ?_⟩
  rw [← ℱ.map_comap_of_surjective f_surj, ← mapClusterPt_comp] at h
  rcases hgf.clusterPt_of_mapClusterPt h with ⟨x, rfl, hx⟩
  rw [← ℱ.map_comap_of_surjective f_surj]
  exact ⟨f x, rfl, hx.map hf.continuousAt tendsto_map⟩
lemma isProperMap_of_comp_of_inj {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) (g_inj : g.Injective) : IsProperMap f := by
  refine ⟨hf, fun ℱ y h ↦ ?_⟩
  rcases hgf.clusterPt_of_mapClusterPt (h.map hg.continuousAt tendsto_map) with ⟨x, hx1, hx2⟩
  exact ⟨x, g_inj hx1, hx2⟩
lemma isProperMap_of_comp_of_t2 [T2Space Y] (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) : IsProperMap f := by
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨hf, fun 𝒰 y h ↦ ?_⟩
  rw [isProperMap_iff_ultrafilter] at hgf
  rcases hgf.2 ((hg.tendsto y).comp h) with ⟨x, -, hx⟩
  exact ⟨x, hx⟩
lemma IsProperMap.prodMap {g : Z → W} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (Prod.map f g) := by
  simp_rw [isProperMap_iff_ultrafilter] at hf hg ⊢
  constructor
  · exact hf.1.prodMap hg.1
  · intro 𝒰 ⟨y, w⟩ hyw
    simp_rw [nhds_prod_eq, tendsto_prod_iff'] at hyw
    rcases hf.2 (show Tendsto f (Ultrafilter.map fst 𝒰) (𝓝 y) by simpa using hyw.1) with
      ⟨x, hxy, hx⟩
    rcases hg.2 (show Tendsto g (Ultrafilter.map snd 𝒰) (𝓝 w) by simpa using hyw.2) with
      ⟨z, hzw, hz⟩
    refine ⟨⟨x, z⟩, Prod.ext hxy hzw, ?_⟩
    rw [nhds_prod_eq, le_prod]
    exact ⟨hx, hz⟩
@[deprecated (since := "2024-10-06")] alias IsProperMap.prod_map := IsProperMap.prodMap
lemma IsProperMap.pi_map {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : (i : ι) → X i → Y i} (h : ∀ i, IsProperMap (f i)) :
    IsProperMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  simp_rw [isProperMap_iff_ultrafilter] at h ⊢
  constructor
  · exact continuous_pi fun i ↦ (h i).1.comp (continuous_apply i)
  · intro 𝒰 y hy
    have : ∀ i, Tendsto (f i) (Ultrafilter.map (eval i) 𝒰) (𝓝 (y i)) := by
      simpa [tendsto_pi_nhds] using hy
    choose x hxy hx using fun i ↦ (h i).2 (this i)
    refine ⟨x, funext hxy, ?_⟩
    rwa [nhds_pi, le_pi]
lemma IsProperMap.isCompact_preimage (h : IsProperMap f) {K : Set Y} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  rw [← comap_principal, ← map_le_iff_le_comap, ← Ultrafilter.coe_map] at h𝒰
  rcases hK.ultrafilter_le_nhds _ h𝒰 with ⟨y, hyK, hy⟩
  rcases h.ultrafilter_le_nhds_of_tendsto hy with ⟨x, rfl, hx⟩
  exact ⟨x, hyK, hx⟩
theorem isProperMap_iff_isClosedMap_and_compact_fibers :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ ∀ y, IsCompact (f ⁻¹' {y}) := by
  constructor <;> intro H
  · exact ⟨H.continuous, H.isClosedMap, fun y ↦ H.isCompact_preimage isCompact_singleton⟩
  · rw [isProperMap_iff_clusterPt]
    refine ⟨H.1, fun ℱ y hy ↦ ?_⟩
    rw [H.2.1.mapClusterPt_iff_lift'_closure H.1] at hy
    rcases H.2.2 y (f := Filter.lift' ℱ closure ⊓ 𝓟 (f ⁻¹' {y})) inf_le_right with ⟨x, hxy, hx⟩
    refine ⟨x, hxy, ?_⟩
    rw [← clusterPt_lift'_closure_iff]
    exact hx.mono inf_le_left
lemma isProperMap_iff_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective) :
    IsProperMap f ↔ IsClosedMap f := by
  refine ⟨fun h ↦ h.isClosedMap, fun h ↦ ?_⟩
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  exact ⟨f_cont, h, fun y ↦ (subsingleton_singleton.preimage f_inj).isCompact⟩
lemma isProperMap_of_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective)
    (f_closed : IsClosedMap f) : IsProperMap f :=
  (isProperMap_iff_isClosedMap_of_inj f_cont f_inj).2 f_closed
@[simp] lemma Homeomorph.isProperMap (e : X ≃ₜ Y) : IsProperMap e :=
  isProperMap_of_isClosedMap_of_inj e.continuous e.injective e.isClosedMap
protected lemma IsHomeomorph.isProperMap (hf : IsHomeomorph f) : IsProperMap f :=
  isProperMap_of_isClosedMap_of_inj hf.continuous hf.injective hf.isClosedMap
@[simp] lemma isProperMap_id : IsProperMap (id : X → X) := IsHomeomorph.id.isProperMap
lemma Topology.IsClosedEmbedding.isProperMap (hf : IsClosedEmbedding f) : IsProperMap f :=
  isProperMap_of_isClosedMap_of_inj hf.continuous hf.injective hf.isClosedMap
@[deprecated (since := "2024-10-20")]
alias isProperMap_of_closedEmbedding := IsClosedEmbedding.isProperMap
lemma IsClosed.isProperMap_subtypeVal {C : Set X} (hC : IsClosed C) : IsProperMap ((↑) : C → X) :=
  hC.isClosedEmbedding_subtypeVal.isProperMap
@[deprecated (since := "2024-10-20")]
alias isProperMap_subtype_val_of_closed := IsClosed.isProperMap_subtypeVal
lemma IsProperMap.restrict {C : Set X} (hf : IsProperMap f) (hC : IsClosed C) :
    IsProperMap fun x : C ↦ f x := hC.isProperMap_subtypeVal.comp  hf
@[deprecated (since := "2024-10-20")]
alias isProperMap_restr_of_proper_of_closed := IsProperMap.restrict
lemma IsProperMap.isClosed_range (hf : IsProperMap f) : IsClosed (range f) :=
  hf.isClosedMap.isClosed_range
@[deprecated (since := "2024-05-08")] alias IsProperMap.closed_range := IsProperMap.isClosed_range
lemma isProperMap_iff_isClosedMap_and_tendsto_cofinite [T1Space Y] :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ Tendsto f (cocompact X) cofinite := by
  simp_rw [isProperMap_iff_isClosedMap_and_compact_fibers, Tendsto,
    le_cofinite_iff_compl_singleton_mem, mem_map, preimage_compl]
  refine and_congr_right fun f_cont ↦ and_congr_right fun _ ↦
    ⟨fun H y ↦ (H y).compl_mem_cocompact, fun H y ↦ ?_⟩
  rcases mem_cocompact.mp (H y) with ⟨K, hK, hKy⟩
  exact hK.of_isClosed_subset (isClosed_singleton.preimage f_cont)
    (compl_le_compl_iff_le.mp hKy)
theorem Continuous.isProperMap [CompactSpace X] [T2Space Y] (hf : Continuous f) : IsProperMap f :=
  isProperMap_iff_isClosedMap_and_tendsto_cofinite.2 ⟨hf, hf.isClosedMap, by simp⟩
theorem IsProperMap.universally_closed (Z) [TopologicalSpace Z] (h : IsProperMap f) :
    IsClosedMap (Prod.map f id : X × Z → Y × Z) :=
  (h.prodMap isProperMap_id).isClosedMap
theorem isProperMap_iff_isClosedMap_filter {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap
      (Prod.map f id : X × Filter X → Y × Filter X) := by
  constructor <;> intro H
  · exact ⟨H.continuous, H.universally_closed _⟩
  · rw [isProperMap_iff_ultrafilter]
    refine ⟨H.1, fun 𝒰 y hy ↦ ?_⟩
    let F : Set (X × Filter X) := closure {xℱ | xℱ.2 = pure xℱ.1}
    have := H.2 F isClosed_closure
    have : (y, ↑𝒰) ∈ Prod.map f id '' F :=
      this.mem_of_tendsto (hy.prod_mk_nhds (Filter.tendsto_pure_self (𝒰 : Filter X)))
        (Eventually.of_forall fun x ↦ ⟨⟨x, pure x⟩, subset_closure rfl, rfl⟩)
    rcases this with ⟨⟨x, _⟩, hx, ⟨_, _⟩⟩
    refine ⟨x, rfl, fun U hU ↦ Ultrafilter.compl_not_mem_iff.mp fun hUc ↦ ?_⟩
    rw [mem_closure_iff_nhds] at hx
    rcases hx (U ×ˢ {𝒢 | Uᶜ ∈ 𝒢}) (prod_mem_nhds hU (isOpen_setOf_mem.mem_nhds hUc)) with
      ⟨⟨z, 𝒢⟩, ⟨⟨hz : z ∈ U, hz' : Uᶜ ∈ 𝒢⟩, rfl : 𝒢 = pure z⟩⟩
    exact hz' hz