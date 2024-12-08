import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
open Bornology Filter Function Set TopologicalSpace Topology
open scoped Uniformity
variable {X Y : Type*}
section TopologicalSpace
variable [TopologicalSpace X] [TopologicalSpace Y]
theorem subset_seqClosure {s : Set X} : s ⊆ seqClosure s := fun p hp =>
  ⟨const ℕ p, fun _ => hp, tendsto_const_nhds⟩
theorem seqClosure_subset_closure {s : Set X} : seqClosure s ⊆ closure s := fun _p ⟨_x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)
theorem IsSeqClosed.seqClosure_eq {s : Set X} (hs : IsSeqClosed s) : seqClosure s = s :=
  Subset.antisymm (fun _p ⟨_x, hx, hp⟩ => hs hx hp) subset_seqClosure
theorem isSeqClosed_of_seqClosure_eq {s : Set X} (hs : seqClosure s = s) : IsSeqClosed s :=
  fun x _p hxs hxp => hs ▸ ⟨x, hxs, hxp⟩
theorem isSeqClosed_iff {s : Set X} : IsSeqClosed s ↔ seqClosure s = s :=
  ⟨IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq⟩
protected theorem IsClosed.isSeqClosed {s : Set X} (hc : IsClosed s) : IsSeqClosed s :=
  fun _u _x hu hx => hc.mem_of_tendsto hx (Eventually.of_forall hu)
theorem seqClosure_eq_closure [FrechetUrysohnSpace X] (s : Set X) : seqClosure s = closure s :=
  seqClosure_subset_closure.antisymm <| FrechetUrysohnSpace.closure_subset_seqClosure s
theorem mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) := by
  rw [← seqClosure_eq_closure]
  rfl
theorem tendsto_nhds_iff_seq_tendsto [FrechetUrysohnSpace X] {f : X → Y} {a : X} {b : Y} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 b) := by
  refine
    ⟨fun hf u hu => hf.comp hu, fun h =>
      ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 ?_⟩
  rintro s ⟨hbs, hsc⟩
  refine ⟨closure (f ⁻¹' s), ⟨mt ?_ hbs, isClosed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seqClosure_eq_closure]
  rintro ⟨u, hus, hu⟩
  exact hsc.mem_of_tendsto (h u hu) (Eventually.of_forall hus)
theorem FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
    (h : ∀ (f : X → Prop) (a : X),
      (∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 (f a))) → ContinuousAt f a) :
    FrechetUrysohnSpace X := by
  refine ⟨fun s x hcx => ?_⟩
  by_cases hx : x ∈ s
  · exact subset_seqClosure hx
  · obtain ⟨u, hux, hus⟩ : ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧ ∃ᶠ x in atTop, u x ∈ s := by
      simpa only [ContinuousAt, hx, tendsto_nhds_true, (· ∘ ·), ← not_frequently, exists_prop,
        ← mem_closure_iff_frequently, hcx, imp_false, not_forall, not_not, not_false_eq_true,
        not_true_eq_false] using h (· ∉ s) x
    rcases extraction_of_frequently_atTop hus with ⟨φ, φ_mono, hφ⟩
    exact ⟨u ∘ φ, hφ, hux.comp φ_mono.tendsto_atTop⟩
instance (priority := 100) FirstCountableTopology.frechetUrysohnSpace
    [FirstCountableTopology X] : FrechetUrysohnSpace X :=
  FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto fun _ _ => tendsto_iff_seq_tendsto.2
instance (priority := 100) FrechetUrysohnSpace.to_sequentialSpace [FrechetUrysohnSpace X] :
    SequentialSpace X :=
  ⟨fun s hs => by rw [← closure_eq_iff_isClosed, ← seqClosure_eq_closure, hs.seqClosure_eq]⟩
theorem Topology.IsInducing.frechetUrysohnSpace [FrechetUrysohnSpace Y] {f : X → Y}
    (hf : IsInducing f) : FrechetUrysohnSpace X := by
  refine ⟨fun s x hx ↦ ?_⟩
  rw [hf.closure_eq_preimage_closure_image, mem_preimage, mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨u, hus, hu⟩
  choose v hv hvu using hus
  refine ⟨v, hv, ?_⟩
  simpa only [hf.tendsto_nhds_iff, Function.comp_def, hvu]
@[deprecated (since := "2024-10-28")]
alias Inducing.frechetUrysohnSpace := IsInducing.frechetUrysohnSpace
instance Subtype.instFrechetUrysohnSpace [FrechetUrysohnSpace X] {p : X → Prop} :
    FrechetUrysohnSpace (Subtype p) :=
  IsInducing.subtypeVal.frechetUrysohnSpace
theorem isSeqClosed_iff_isClosed [SequentialSpace X] {M : Set X} : IsSeqClosed M ↔ IsClosed M :=
  ⟨IsSeqClosed.isClosed, IsClosed.isSeqClosed⟩
theorem IsSeqClosed.preimage {f : X → Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f) :
    IsSeqClosed (f ⁻¹' s) := fun _x _p hx hp => hs hx (hf hp)
protected theorem Continuous.seqContinuous {f : X → Y} (hf : Continuous f) : SeqContinuous f :=
  fun _x p hx => (hf.tendsto p).comp hx
protected theorem SeqContinuous.continuous [SequentialSpace X] {f : X → Y} (hf : SeqContinuous f) :
    Continuous f :=
  continuous_iff_isClosed.mpr fun _s hs => (hs.isSeqClosed.preimage hf).isClosed
theorem continuous_iff_seqContinuous [SequentialSpace X] {f : X → Y} :
    Continuous f ↔ SeqContinuous f :=
  ⟨Continuous.seqContinuous, SeqContinuous.continuous⟩
theorem SequentialSpace.coinduced [SequentialSpace X] {Y} (f : X → Y) :
    @SequentialSpace Y (.coinduced f ‹_›) :=
  letI : TopologicalSpace Y := .coinduced f ‹_›
  ⟨fun _ hs ↦ isClosed_coinduced.2 (hs.preimage continuous_coinduced_rng.seqContinuous).isClosed⟩
protected theorem SequentialSpace.iSup {X} {ι : Sort*} {t : ι → TopologicalSpace X}
    (h : ∀ i, @SequentialSpace X (t i)) : @SequentialSpace X (⨆ i, t i) := by
  letI : TopologicalSpace X := ⨆ i, t i
  refine ⟨fun s hs ↦ isClosed_iSup_iff.2 fun i ↦ ?_⟩
  letI := t i
  exact IsSeqClosed.isClosed fun u x hus hux ↦ hs hus <| hux.mono_right <| nhds_mono <| le_iSup _ _
protected theorem SequentialSpace.sup {X} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @SequentialSpace X t₁) (h₂ : @SequentialSpace X t₂) :
    @SequentialSpace X (t₁ ⊔ t₂) := by
  rw [sup_eq_iSup]
  exact .iSup <| Bool.forall_bool.2 ⟨h₂, h₁⟩
lemma Topology.IsQuotientMap.sequentialSpace [SequentialSpace X] {f : X → Y}
    (hf : IsQuotientMap f) : SequentialSpace Y := hf.2.symm ▸ .coinduced f
@[deprecated (since := "2024-10-22")]
alias QuotientMap.sequentialSpace := IsQuotientMap.sequentialSpace
instance Quotient.instSequentialSpace [SequentialSpace X] {s : Setoid X} :
    SequentialSpace (Quotient s) :=
  isQuotientMap_quot_mk.sequentialSpace
instance Sum.instSequentialSpace [SequentialSpace X] [SequentialSpace Y] :
    SequentialSpace (X ⊕ Y) :=
  .sup (.coinduced Sum.inl) (.coinduced Sum.inr)
instance Sigma.instSequentialSpace {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, SequentialSpace (X i)] : SequentialSpace (Σ i, X i) :=
  .iSup fun _ ↦ .coinduced _
end TopologicalSpace
section SeqCompact
open TopologicalSpace FirstCountableTopology
variable [TopologicalSpace X]
theorem IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_atTop hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩
theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : ℕ → X) :
    ∃ (a : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨a, _, φ, mono, h⟩ := isSeqCompact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩
section FirstCountableTopology
variable [FirstCountableTopology X]
open FirstCountableTopology
protected theorem IsCompact.isSeqCompact {s : Set X} (hs : IsCompact s) : IsSeqCompact s :=
  fun _x x_in =>
  let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (Eventually.of_forall x_in))
  ⟨a, a_in, tendsto_subseq ha⟩
theorem IsCompact.tendsto_subseq' {s : Set X} {x : ℕ → X} (hs : IsCompact s)
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact.subseq_of_frequently_in hx
theorem IsCompact.tendsto_subseq {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact hx
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace X] :
    SeqCompactSpace X :=
  ⟨isCompact_univ.isSeqCompact⟩
theorem CompactSpace.tendsto_subseq [CompactSpace X] (x : ℕ → X) :
    ∃ (a : _) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  SeqCompactSpace.tendsto_subseq x
end FirstCountableTopology
section Image
variable [TopologicalSpace Y] {f : X → Y}
theorem IsSeqCompact.image (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) :
    IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  choose xs xs_in_K fxs_eq_ys using ys_in_fK
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨f a, mem_image_of_mem f a_in_K, phi, phi_mono, ?_⟩
  exact (f_cont xs_phi_lim).congr fun x ↦ fxs_eq_ys (phi x)
theorem IsSeqCompact.range [SeqCompactSpace X] (f_cont : SeqContinuous f) :
    IsSeqCompact (Set.range f) := by
  simpa using isSeqCompact_univ.image f_cont
end Image
end SeqCompact
section UniformSpaceSeqCompact
open uniformity
open UniformSpace Prod
variable [UniformSpace X] {s : Set X}
theorem IsSeqCompact.exists_tendsto_of_frequently_mem (hs : IsSeqCompact s) {u : ℕ → X}
    (hu : ∃ᶠ n in atTop, u n ∈ s) (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  let ⟨x, hxs, _φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
  ⟨x, hxs, tendsto_nhds_of_cauchySeq_of_subseq huc φ_mono.tendsto_atTop hx⟩
theorem IsSeqCompact.exists_tendsto (hs : IsSeqCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s)
    (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  hs.exists_tendsto_of_frequently_mem (Frequently.of_forall hu) huc
protected theorem IsSeqCompact.totallyBounded (h : IsSeqCompact s) : TotallyBounded s := by
  intro V V_in
  unfold IsSeqCompact at h
  contrapose! h
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ ∀ n m, m < n → u m ∉ ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using seq_of_forall_finite_exists h
  refine ⟨u, u_in, fun x _ φ hφ huφ => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V :=
    huφ.cauchySeq.mem_entourage V_in
  exact hu (φ <| N + 1) (φ N) (hφ <| Nat.lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)
variable [IsCountablyGenerated (𝓤 X)]
protected theorem IsSeqCompact.isComplete (hs : IsSeqCompact s) : IsComplete s := fun l hl hls => by
  have := hl.1
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩
  choose W hW hWV using fun n => comp_mem_uniformity_sets (hV.mem n)
  have hWV' : ∀ n, W n ⊆ V n := fun n ⟨x, y⟩ hx =>
    @hWV n (x, y) ⟨x, refl_mem_uniformity <| hW _, hx⟩
  obtain ⟨t, ht_anti, htl, htW, hts⟩ :
      ∃ t : ℕ → Set X, Antitone t ∧ (∀ n, t n ∈ l) ∧ (∀ n, t n ×ˢ t n ⊆ W n) ∧ ∀ n, t n ⊆ s := by
    have : ∀ n, ∃ t ∈ l, t ×ˢ t ⊆ W n ∧ t ⊆ s := by
      rw [le_principal_iff] at hls
      have : ∀ n, W n ∩ s ×ˢ s ∈ l ×ˢ l := fun n => inter_mem (hl.2 (hW n)) (prod_mem_prod hls hls)
      simpa only [l.basis_sets.prod_self.mem_iff, true_imp_iff, subset_inter_iff,
        prod_self_subset_prod_self, and_assoc] using this
    choose t htl htW hts using this
    have : ∀ n : ℕ, ⋂ k ≤ n, t k ⊆ t n := fun n => by apply iInter₂_subset; rfl
    exact ⟨fun n => ⋂ k ≤ n, t k, fun m n h =>
      biInter_subset_biInter_left fun k (hk : k ≤ m) => hk.trans h, fun n =>
      (biInter_mem (finite_le_nat n)).2 fun k _ => htl k, fun n =>
      (prod_mono (this n) (this n)).trans (htW n), fun n => (this n).trans (hts n)⟩
  choose u hu using fun n => Filter.nonempty_of_mem (htl n)
  have huc : CauchySeq u := hV.toHasBasis.cauchySeq_iff.2 fun N _ =>
      ⟨N, fun m hm n hn => hWV' _ <| @htW N (_, _) ⟨ht_anti hm (hu _), ht_anti hn (hu _)⟩⟩
  rcases hs.exists_tendsto (fun n => hts n (hu n)) huc with ⟨x, hxs, hx⟩
  refine ⟨x, hxs, (nhds_basis_uniformity' hV.toHasBasis).ge_iff.2 fun N _ => ?_⟩
  obtain ⟨n, hNn, hn⟩ : ∃ n, N ≤ n ∧ u n ∈ ball x (W N) :=
    ((eventually_ge_atTop N).and (hx <| ball_mem_nhds x (hW N))).exists
  refine mem_of_superset (htl n) fun y hy => hWV N ⟨u n, hn, htW N ?_⟩
  exact ⟨ht_anti hNn (hu n), ht_anti hNn hy⟩
protected theorem IsSeqCompact.isCompact (hs : IsSeqCompact s) : IsCompact s :=
  isCompact_iff_totallyBounded_isComplete.2 ⟨hs.totallyBounded, hs.isComplete⟩
protected theorem UniformSpace.isCompact_iff_isSeqCompact : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.isSeqCompact, fun H => H.isCompact⟩
theorem UniformSpace.compactSpace_iff_seqCompactSpace : CompactSpace X ↔ SeqCompactSpace X := by
  simp only [← isCompact_univ_iff, seqCompactSpace_iff, UniformSpace.isCompact_iff_isSeqCompact]
end UniformSpaceSeqCompact