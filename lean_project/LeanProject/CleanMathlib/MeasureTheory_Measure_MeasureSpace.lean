import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Interval.Set.Monotone
noncomputable section
open Set
open Filter hiding map
open Function MeasurableSpace Topology Filter ENNReal NNReal Interval MeasureTheory
open scoped symmDiff
variable {α β γ δ ι R R' : Type*}
namespace MeasureTheory
section
variable {m : MeasurableSpace α} {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}
instance ae_isMeasurablyGenerated : IsMeasurablyGenerated (ae μ) :=
  ⟨fun _s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩
theorem ae_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ ∀ᵐ x ∂μ, x ∈ Ioc b a → P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]
theorem measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀ h.nullMeasurableSet hd.aedisjoint
theorem measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀' h.nullMeasurableSet hd.aedisjoint
theorem measure_inter_add_diff (s : Set α) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s :=
  measure_inter_add_diff₀ _ ht.nullMeasurableSet
theorem measure_diff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ (s ∩ t) = μ s :=
  (add_comm _ _).trans (measure_inter_add_diff s ht)
theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_diff (s ∪ t) ht, Set.union_inter_cancel_right, union_diff_right, ←
    measure_inter_add_diff s ht]
  ac_rfl
theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]
lemma measure_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
  simpa only [symmDiff_def, sup_eq_union]
    using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint
lemma measure_symmDiff_le (s t u : Set α) :
    μ (s ∆ u) ≤ μ (s ∆ t) + μ (t ∆ u) :=
  le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))
theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ :=
  measure_add_measure_compl₀ h.nullMeasurableSet
theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
    (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
  haveI := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2
theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet
theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
    (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion₀ hs hd h]
theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion hs hd h]
theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype]
  exact measure_biUnion₀ s.countable_toSet hd hm
theorem measure_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) :=
  measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet
theorem tsum_meas_le_meas_iUnion_of_disjoint₀ {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) := by
  rw [ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ ↦ Subset.rfl
theorem tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
  tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))
theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.biUnion_preimage_singleton, measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]
lemma measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α → β} (hs : s.Countable) :
    μ (f ⁻¹' s) = 0 ↔ ∀ x ∈ s, μ (f ⁻¹' {x}) = 0 := by
  rw [← biUnion_preimage_singleton, measure_biUnion_null_iff hs]
theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]
theorem measure_diff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_congr <| diff_ae_eq_self.2 h
theorem measure_add_diff (hs : NullMeasurableSet s μ) (t : Set α) :
    μ s + μ (t \ s) = μ (s ∪ t) := by
  rw [← measure_union₀' hs disjoint_sdiff_right.aedisjoint, union_diff_self]
theorem measure_diff' (s : Set α) (hm : NullMeasurableSet t μ) (h_fin : μ t ≠ ∞) :
    μ (s \ t) = μ (s ∪ t) - μ t :=
  ENNReal.eq_sub_of_add_eq h_fin <| by rw [add_comm, measure_add_diff hm, union_comm]
theorem measure_diff (h : s₂ ⊆ s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : μ s₂ ≠ ∞) :
    μ (s₁ \ s₂) = μ s₁ - μ s₂ := by rw [measure_diff' _ h₂ h_fin, union_eq_self_of_subset_right h]
theorem le_measure_diff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
  tsub_le_iff_left.2 <| (measure_le_inter_add_diff μ s₁ s₂).trans <| by
    gcongr; apply inter_subset_right
theorem measure_eq_top_iff_of_symmDiff (hμst : μ (s ∆ t) ≠ ∞) : μ s = ∞ ↔ μ t = ∞ := by
  suffices h : ∀ u v, μ (u ∆ v) ≠ ∞ → μ u = ∞ → μ v = ∞
    from ⟨h s t hμst, h t s (symmDiff_comm s t ▸ hμst)⟩
  intro u v hμuv hμu
  by_contra! hμv
  apply hμuv
  rw [Set.symmDiff_def, eq_top_iff]
  calc
    ∞ = μ u - μ v := by rw [ENNReal.sub_eq_top_iff.2 ⟨hμu, hμv⟩]
    _ ≤ μ (u \ v) := le_measure_diff
    _ ≤ μ (u \ v ∪ v \ u) := measure_mono subset_union_left
theorem measure_ne_top_iff_of_symmDiff (hμst : μ (s ∆ t) ≠ ∞) : μ s ≠ ∞ ↔ μ t ≠ ∞ :=
    (measure_eq_top_iff_of_symmDiff hμst).ne
theorem measure_diff_lt_of_lt_add (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (hs' : μ s ≠ ∞)
    {ε : ℝ≥0∞} (h : μ t < μ s + ε) : μ (t \ s) < ε := by
  rw [measure_diff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h
theorem measure_diff_le_iff_le_add (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (hs' : μ s ≠ ∞)
    {ε : ℝ≥0∞} : μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε := by
  rw [measure_diff hst hs hs', tsub_le_iff_left]
theorem measure_eq_measure_of_null_diff {s t : Set α} (hst : s ⊆ t) (h_nulldiff : μ (t \ s) = 0) :
    μ s = μ t := measure_congr <|
      EventuallyLE.antisymm (HasSubset.Subset.eventuallyLE hst) (ae_le_set.mpr h_nulldiff)
theorem measure_eq_measure_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
    (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ := by
  have le12 : μ s₁ ≤ μ s₂ := measure_mono h12
  have le23 : μ s₂ ≤ μ s₃ := measure_mono h23
  have key : μ s₃ ≤ μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ ∪ s₁) := by rw [diff_union_of_subset (h12.trans h23)]
      _ ≤ μ (s₃ \ s₁) + μ s₁ := measure_union_le _ _
      _ = μ s₁ := by simp only [h_nulldiff, zero_add]
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩
theorem measure_eq_measure_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).1
theorem measure_eq_measure_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₂ = μ s₃ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).2
lemma measure_compl₀ (h : NullMeasurableSet s μ) (hs : μ s ≠ ∞) :
    μ sᶜ = μ Set.univ - μ s := by
  rw [← measure_add_measure_compl₀ h, ENNReal.add_sub_cancel_left hs]
theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) : μ sᶜ = μ univ - μ s :=
  measure_compl₀ h₁.nullMeasurableSet h_fin
lemma measure_inter_conull' (ht : μ (s \ t) = 0) : μ (s ∩ t) = μ s := by
  rw [← diff_compl, measure_diff_null']; rwa [← diff_eq]
lemma measure_inter_conull (ht : μ tᶜ = 0) : μ (s ∩ t) = μ s := by
  rw [← diff_compl, measure_diff_null ht]
@[simp]
theorem union_ae_eq_left_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] s ↔ t ≤ᵐ[μ] s := by
  rw [ae_le_set]
  refine
    ⟨fun h => by simpa only [union_diff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_diff_left],
          HasSubset.Subset.eventuallyLE subset_union_left⟩⟩
@[simp]
theorem union_ae_eq_right_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] t ↔ s ≤ᵐ[μ] t := by
  rw [union_comm, union_ae_eq_left_iff_ae_subset]
theorem ae_eq_of_ae_subset_of_measure_ge (h₁ : s ≤ᵐ[μ] t) (h₂ : μ t ≤ μ s)
    (hsm : NullMeasurableSet s μ) (ht : μ t ≠ ∞) : s =ᵐ[μ] t := by
  refine eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr ?_⟩
  replace h₂ : μ t = μ s := h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s ≠ ∞ := h₂ ▸ ht
  rw [measure_diff' t hsm ht, measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁), h₂, tsub_self]
theorem ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : NullMeasurableSet s μ)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
  ae_eq_of_ae_subset_of_measure_ge (HasSubset.Subset.eventuallyLE h₁) h₂ hsm ht
theorem measure_iUnion_congr_of_subset {ι : Sort*} [Countable ι] {s : ι → Set α} {t : ι → Set α}
    (hsub : ∀ i, s i ⊆ t i) (h_le : ∀ i, μ (t i) ≤ μ (s i)) : μ (⋃ i, s i) = μ (⋃ i, t i) := by
  refine le_antisymm (by gcongr; apply hsub) ?_
  rcases Classical.em (∃ i, μ (t i) = ∞) with (⟨i, hi⟩ | htop)
  · calc
      μ (⋃ i, t i) ≤ ∞ := le_top
      _ ≤ μ (s i) := hi ▸ h_le i
      _ ≤ μ (⋃ i, s i) := measure_mono <| subset_iUnion _ _
  push_neg at htop
  set M := toMeasurable μ
  have H : ∀ b, (M (t b) ∩ M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) := by
    refine fun b => ae_eq_of_subset_of_measure_ge inter_subset_left ?_ ?_ ?_
    · calc
        μ (M (t b)) = μ (t b) := measure_toMeasurable _
        _ ≤ μ (s b) := h_le b
        _ ≤ μ (M (t b) ∩ M (⋃ b, s b)) :=
          measure_mono <|
            subset_inter ((hsub b).trans <| subset_toMeasurable _ _)
              ((subset_iUnion _ _).trans <| subset_toMeasurable _ _)
    · measurability
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) ≤ μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) ∩ M (⋃ b, s b)) := measure_congr (EventuallyEq.countable_iUnion H).symm
    _ ≤ μ (M (⋃ b, s b)) := measure_mono (iUnion_subset fun b => inter_subset_right)
    _ = μ (⋃ b, s b) := measure_toMeasurable _
theorem measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂) (hsμ : μ s₂ ≤ μ s₁)
    (ht : t₁ ⊆ t₂) (htμ : μ t₂ ≤ μ t₁) : μ (s₁ ∪ t₁) = μ (s₂ ∪ t₂) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)
@[simp]
theorem measure_iUnion_toMeasurable {ι : Sort*} [Countable ι] (s : ι → Set α) :
    μ (⋃ i, toMeasurable μ (s i)) = μ (⋃ i, s i) :=
  Eq.symm <| measure_iUnion_congr_of_subset (fun _i => subset_toMeasurable _ _) fun _i ↦
    (measure_toMeasurable _).le
theorem measure_biUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β → Set α) :
    μ (⋃ b ∈ I, toMeasurable μ (s b)) = μ (⋃ b ∈ I, s b) := by
  haveI := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]
@[simp]
theorem measure_toMeasurable_union : μ (toMeasurable μ s ∪ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl
@[simp]
theorem measure_union_toMeasurable : μ (s ∪ toMeasurable μ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le
theorem sum_measure_le_measure_univ {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, NullMeasurableSet (t i) μ) (H : Set.Pairwise s (AEDisjoint μ on t)) :
    (∑ i ∈ s, μ (t i)) ≤ μ (univ : Set α) := by
  rw [← measure_biUnion_finset₀ H h]
  exact measure_mono (subset_univ _)
theorem tsum_measure_le_measure_univ {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ)
    (H : Pairwise (AEDisjoint μ on s)) : ∑' i, μ (s i) ≤ μ (univ : Set α) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace α}
    (μ : Measure α) {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ)
    (H : μ (univ : Set α) < ∑' i, μ (s i)) : ∃ i j, i ≠ j ∧ (s i ∩ s j).Nonempty := by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i j hij)).aedisjoint
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Measure α)
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, NullMeasurableSet (t i) μ)
    (H : μ (univ : Set α) < ∑ i ∈ s, μ (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)).aedisjoint
theorem nonempty_inter_of_measure_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s ∪ t) := (measure_union h ht).symm
    _ ≤ μ u := measure_mono (union_subset h's h't)
theorem nonempty_inter_of_measure_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h
theorem _root_.Directed.measure_iUnion [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  rcases Countable.exists_injective_nat ι with ⟨e, he⟩
  generalize ht : Function.extend e s ⊥ = t
  replace hd : Directed (· ⊆ ·) t := ht ▸ hd.extend_bot he
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n) by
    simp only [← ht, Function.apply_extend μ, ← iSup_eq_iUnion, iSup_extend_bot he,
      Function.comp_def, Pi.bot_apply, bot_eq_empty, measure_empty] at this
    exact this.trans (iSup_extend_bot he _)
  clear! ι
  refine le_antisymm ?_ (iSup_le fun i ↦ measure_mono <| subset_iUnion _ _)
  set T : ℕ → Set α := fun n => toMeasurable μ (t n)
  set Td : ℕ → Set α := disjointed T
  have hm : ∀ n, MeasurableSet (Td n) := .disjointed fun n ↦ measurableSet_toMeasurable _ _
  calc
    μ (⋃ n, t n) = μ (⋃ n, Td n) := by rw [iUnion_disjointed, measure_iUnion_toMeasurable]
    _ ≤ ∑' n, μ (Td n) := measure_iUnion_le _
    _ = ⨆ I : Finset ℕ, ∑ n ∈ I, μ (Td n) := ENNReal.tsum_eq_iSup_sum
    _ ≤ ⨆ n, μ (t n) := iSup_le fun I => by
      rcases hd.finset_le I with ⟨N, hN⟩
      calc
        (∑ n ∈ I, μ (Td n)) = μ (⋃ n ∈ I, Td n) :=
          (measure_biUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
        _ ≤ μ (⋃ n ∈ I, T n) := measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ = μ (⋃ n ∈ I, t n) := measure_biUnion_toMeasurable I.countable_toSet _
        _ ≤ μ (t N) := measure_mono (iUnion₂_subset hN)
        _ ≤ ⨆ n, μ (t n) := le_iSup (μ ∘ t) N
@[deprecated (since := "2024-09-01")] alias measure_iUnion_eq_iSup := Directed.measure_iUnion
theorem _root_.Monotone.measure_iUnion [Preorder ι] [IsDirected ι (· ≤ ·)]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Monotone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ =>
    rcases exists_seq_monotone_tendsto_atTop_atTop ι with ⟨x, hxm, hx⟩
    rw [← hs.iUnion_comp_tendsto_atTop hx, ← Monotone.iSup_comp_tendsto_atTop _ hx]
    exacts [(hs.comp hxm).directed_le.measure_iUnion, fun _ _ h ↦ measure_mono (hs h)]
theorem _root_.Antitone.measure_iUnion [Preorder ι] [IsDirected ι (· ≥ ·)]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Antitone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) :=
  hs.dual_left.measure_iUnion
theorem measure_iUnion_eq_iSup_accumulate [Preorder ι] [IsDirected ι (· ≤ ·)]
    [(atTop : Filter ι).IsCountablyGenerated] {f : ι → Set α} :
    μ (⋃ i, f i) = ⨆ i, μ (Accumulate f i) := by
  rw [← iUnion_accumulate]
  exact monotone_accumulate.measure_iUnion
@[deprecated (since := "2024-09-01")]
alias measure_iUnion_eq_iSup' := measure_iUnion_eq_iSup_accumulate
theorem measure_biUnion_eq_iSup {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (hd : DirectedOn ((· ⊆ ·) on s) t) : μ (⋃ i ∈ t, s i) = ⨆ i ∈ t, μ (s i) := by
  haveI := ht.to_subtype
  rw [biUnion_eq_iUnion, hd.directed_val.measure_iUnion, ← iSup_subtype'']
theorem _root_.Directed.measure_iInter [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) (hd : Directed (· ⊇ ·) s) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  rcases hfin with ⟨k, hk⟩
  have : ∀ t ⊆ s k, μ t ≠ ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (iInf_le (fun i => μ (s i)) k), ENNReal.sub_iInf, ←
    ENNReal.sub_sub_cancel hk (measure_mono (iInter_subset _ k)), ←
    measure_diff (iInter_subset _ k) (.iInter h) (this _ (iInter_subset _ k)),
    diff_iInter, Directed.measure_iUnion]
  · congr 1
    refine le_antisymm (iSup_mono' fun i => ?_) (iSup_mono fun i => le_measure_diff)
    rcases hd i k with ⟨j, hji, hjk⟩
    use j
    rw [← measure_diff hjk (h _) (this _ hjk)]
    gcongr
  · exact hd.mono_comp _ fun _ _ => diff_subset_diff_right
@[deprecated (since := "2024-09-30")] alias measure_iInter_eq_iInf := Directed.measure_iInter
theorem _root_.Monotone.measure_iInter [Preorder ι] [IsDirected ι (· ≥ ·)]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Monotone s)
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  refine le_antisymm (le_iInf fun i ↦ measure_mono <| iInter_subset _ _) ?_
  have := hfin.nonempty
  rcases exists_seq_antitone_tendsto_atTop_atBot ι with ⟨x, hxm, hx⟩
  calc
    ⨅ i, μ (s i) ≤ ⨅ n, μ (s (x n)) := le_iInf_comp (μ ∘ s) x
    _ = μ (⋂ n, s (x n)) := by
      refine .symm <| (hs.comp_antitone hxm).directed_ge.measure_iInter (fun n ↦ hsm _) ?_
      rcases hfin with ⟨k, hk⟩
      rcases (hx.eventually_le_atBot k).exists with ⟨n, hn⟩
      exact ⟨n, ne_top_of_le_ne_top hk <| measure_mono <| hs hn⟩
    _ ≤ μ (⋂ i, s i) := by
      refine measure_mono <| iInter_mono' fun i ↦ ?_
      rcases (hx.eventually_le_atBot i).exists with ⟨n, hn⟩
      exact ⟨n, hs hn⟩
theorem _root_.Antitone.measure_iInter [Preorder ι] [IsDirected ι (· ≤ ·)]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Antitone s)
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) :=
  hs.dual_left.measure_iInter hsm hfin
theorem measure_iInter_eq_iInf_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α}
    {μ : Measure α} [Countable ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    {f : ι → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) (hfin : ∃ i, μ (f i) ≠ ∞) :
    μ (⋂ i, f i) = ⨅ i, μ (⋂ j ≤ i, f j) := by
  rw [← Antitone.measure_iInter]
  · rw [iInter_comm]
    exact congrArg μ <| iInter_congr fun i ↦ (biInf_const nonempty_Ici).symm
  · exact fun i j h ↦ biInter_mono (Iic_subset_Iic.2 h) fun _ _ ↦ Set.Subset.rfl
  · exact fun i ↦ .biInter (to_countable _) fun _ _ ↦ h _
  · refine hfin.imp fun k hk ↦ ne_top_of_le_ne_top hk <| measure_mono <| iInter₂_subset k ?_
    rfl
@[deprecated (since := "2024-09-30")]
alias measure_iInter_eq_iInf' := measure_iInter_eq_iInf_measure_iInter_le
theorem tendsto_measure_iUnion_atTop [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {s : ι → Set α} (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iUnion]
  exact tendsto_atTop_iSup fun n m hnm => measure_mono <| hm hnm
@[deprecated (since := "2024-09-01")] alias tendsto_measure_iUnion := tendsto_measure_iUnion_atTop
theorem tendsto_measure_iUnion_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    {s : ι → Set α} (hm : Antitone s) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋃ n, s n))) :=
  tendsto_measure_iUnion_atTop (ι := ιᵒᵈ) hm.dual_left
theorem tendsto_measure_iUnion_accumulate {α ι : Type*}
    [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {_ : MeasurableSpace α} {μ : Measure α} {f : ι → Set α} :
    Tendsto (fun i ↦ μ (Accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij ↦ by gcongr
@[deprecated (since := "2024-09-01")]
alias tendsto_measure_iUnion' := tendsto_measure_iUnion_accumulate
theorem tendsto_measure_iInter_atTop [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {s : ι → Set α}
    (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iInter hs hf]
  exact tendsto_atTop_iInf fun n m hnm => measure_mono <| hm hnm
@[deprecated (since := "2024-09-30")]
alias tendsto_measure_iInter := tendsto_measure_iInter_atTop
theorem tendsto_measure_iInter_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Monotone s)
    (hf : ∃ i, μ (s i) ≠ ∞) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋂ n, s n))) :=
  tendsto_measure_iInter_atTop (ι := ιᵒᵈ) hs hm.dual_left hf
theorem tendsto_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [Countable ι] [Preorder ι] {f : ι → Set α} (hm : ∀ i, NullMeasurableSet (f i) μ)
    (hf : ∃ i, μ (f i) ≠ ∞) :
    Tendsto (fun i ↦ μ (⋂ j ≤ i, f j)) atTop (𝓝 (μ (⋂ i, f i))) := by
  refine .of_neBot_imp fun hne ↦ ?_
  cases' atTop_neBot_iff.mp hne
  rw [measure_iInter_eq_iInf_measure_iInter_le hm hf]
  exact tendsto_atTop_iInf
    fun i j hij ↦ measure_mono <| biInter_subset_biInter_left fun k hki ↦ le_trans hki hij
theorem tendsto_measure_biInter_gt {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] {s : ι → Set α}
    {a : ι} (hs : ∀ r > a, NullMeasurableSet (s r) μ) (hm : ∀ i j, a < i → i ≤ j → s i ⊆ s j)
    (hf : ∃ r > a, μ (s r) ≠ ∞) : Tendsto (μ ∘ s) (𝓝[Ioi a] a) (𝓝 (μ (⋂ r > a, s r))) := by
  have : (atBot : Filter (Ioi a)).IsCountablyGenerated := by
    rw [← comap_coe_Ioi_nhdsWithin_Ioi]
    infer_instance
  simp_rw [← map_coe_Ioi_atBot, tendsto_map'_iff, ← mem_Ioi, biInter_eq_iInter]
  apply tendsto_measure_iInter_atBot
  · rwa [Subtype.forall]
  · exact fun i j h ↦ hm i j i.2 h
  · simpa only [Subtype.exists, exists_prop]
theorem measure_if {x : β} {t : Set β} {s : Set α} [Decidable (x ∈ t)] :
    μ (if x ∈ t then s else ∅) = indicator t (fun _ => μ s) x := by split_ifs with h <;> simp [h]
end
section OuterMeasure
variable [ms : MeasurableSpace α] {s t : Set α}
def OuterMeasure.toMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) : Measure α :=
  Measure.ofMeasurable (fun s _ => m s) m.empty fun _f hf hd =>
    m.iUnion_eq_of_caratheodory (fun i => h _ (hf i)) hd
theorem le_toOuterMeasure_caratheodory (μ : Measure α) : ms ≤ μ.toOuterMeasure.caratheodory :=
  fun _s hs _t => (measure_inter_add_diff _ hs).symm
@[simp]
theorem toMeasure_toOuterMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) :
    (m.toMeasure h).toOuterMeasure = m.trim :=
  rfl
@[simp]
theorem toMeasure_apply (m : OuterMeasure α) (h : ms ≤ m.caratheodory) {s : Set α}
    (hs : MeasurableSet s) : m.toMeasure h s = m s :=
  m.trim_eq hs
theorem le_toMeasure_apply (m : OuterMeasure α) (h : ms ≤ m.caratheodory) (s : Set α) :
    m s ≤ m.toMeasure h s :=
  m.le_trim s
theorem toMeasure_apply₀ (m : OuterMeasure α) (h : ms ≤ m.caratheodory) {s : Set α}
    (hs : NullMeasurableSet s (m.toMeasure h)) : m.toMeasure h s = m s := by
  refine le_antisymm ?_ (le_toMeasure_apply _ _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
  calc
    m.toMeasure h s = m.toMeasure h t := measure_congr heq.symm
    _ = m t := toMeasure_apply m h htm
    _ ≤ m s := m.mono hts
@[simp]
theorem toOuterMeasure_toMeasure {μ : Measure α} :
    μ.toOuterMeasure.toMeasure (le_toOuterMeasure_caratheodory _) = μ :=
  Measure.ext fun _s => μ.toOuterMeasure.trim_eq
@[simp]
theorem boundedBy_measure (μ : Measure α) : OuterMeasure.boundedBy μ = μ.toOuterMeasure :=
  μ.toOuterMeasure.boundedBy_eq_self
end OuterMeasure
section
variable {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} [MeasurableSpace γ]
variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}
namespace Measure
theorem measure_inter_eq_of_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u)
    (htu : t ⊆ u) (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ (u ∩ s) := by
  rw [h] at ht_ne_top
  refine le_antisymm (by gcongr) ?_
  have A : μ (u ∩ s) + μ (u \ s) ≤ μ (t ∩ s) + μ (u \ s) :=
    calc
      μ (u ∩ s) + μ (u \ s) = μ u := measure_inter_add_diff _ hs
      _ = μ t := h.symm
      _ = μ (t ∩ s) + μ (t \ s) := (measure_inter_add_diff _ hs).symm
      _ ≤ μ (t ∩ s) + μ (u \ s) := by gcongr
  have B : μ (u \ s) ≠ ∞ := (lt_of_le_of_lt (measure_mono diff_subset) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A
theorem measure_toMeasurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm
instance instZero {_ : MeasurableSpace α} : Zero (Measure α) :=
  ⟨{  toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩
@[simp]
theorem zero_toOuterMeasure {_m : MeasurableSpace α} : (0 : Measure α).toOuterMeasure = 0 :=
  rfl
@[simp, norm_cast]
theorem coe_zero {_m : MeasurableSpace α} : ⇑(0 : Measure α) = 0 :=
  rfl
@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_zero
    [ms : MeasurableSpace α] (h : ms ≤ (0 : OuterMeasure α).caratheodory) :
    (0 : OuterMeasure α).toMeasure h = 0 := by
  ext s hs
  simp [hs]
@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero {ms : MeasurableSpace α}
    {μ : OuterMeasure α} (h : ms ≤ μ.caratheodory) : μ.toMeasure h = 0 ↔ μ = 0 where
  mp hμ := by ext s; exact le_bot_iff.1 <| (le_toMeasure_apply _ _ _).trans_eq congr($hμ s)
  mpr := by rintro rfl; simp
@[nontriviality]
lemma apply_eq_zero_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ s = 0 := by
  rw [eq_empty_of_isEmpty s, measure_empty]
instance instSubsingleton [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measure α) :=
  ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩
theorem eq_zero_of_isEmpty [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0
instance instInhabited {_ : MeasurableSpace α} : Inhabited (Measure α) :=
  ⟨0⟩
instance instAdd {_ : MeasurableSpace α} : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add, measure_iUnion hd hs, measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩
@[simp]
theorem add_toOuterMeasure {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl
@[simp, norm_cast]
theorem coe_add {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl
theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl
section SMul
variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
variable [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]
instance instSMul {_ : MeasurableSpace α} : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [OuterMeasure.smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩
@[simp]
theorem smul_toOuterMeasure {_m : MeasurableSpace α} (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl
@[simp, norm_cast]
theorem coe_smul {_m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ :=
  rfl
@[simp]
theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl
instance instSMulCommClass [SMulCommClass R R' ℝ≥0∞] {_ : MeasurableSpace α} :
    SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩
instance instIsScalarTower [SMul R R'] [IsScalarTower R R' ℝ≥0∞] {_ : MeasurableSpace α} :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩
instance instIsCentralScalar [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] {_ : MeasurableSpace α} :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩
end SMul
instance instNoZeroSMulDivisors [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [NoZeroSMulDivisors R ℝ≥0∞] : NoZeroSMulDivisors R (Measure α) where
  eq_zero_or_eq_zero_of_smul_eq_zero h := by simpa [Ne, ext_iff', forall_or_left] using h
instance instMulAction [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure
instance instAddCommMonoid {_ : MeasurableSpace α} : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _
def coeAddHom {_ : MeasurableSpace α} : Measure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
@[simp]
theorem coe_finset_sum {_m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) :
    ⇑(∑ i ∈ I, μ i) = ∑ i ∈ I, ⇑(μ i) := map_sum coeAddHom μ I
theorem finset_sum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) (s : Set α) :
    (∑ i ∈ I, μ i) s = ∑ i ∈ I, μ i s := by rw [coe_finset_sum, Finset.sum_apply]
instance instDistribMulAction [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure
instance instModule [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : Module R (Measure α) :=
  Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure
@[simp]
theorem coe_nnreal_smul_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl
@[simp]
theorem nnreal_smul_coe_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    c • μ s = c * μ s := by
  rfl
theorem ae_smul_measure {p : α → Prop} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : ∀ᵐ x ∂μ, p x) (c : R) : ∀ᵐ x ∂c • μ, p x :=
  ae_iff.2 <| by rw [smul_apply, ae_iff.1 h, ← smul_one_smul ℝ≥0∞, smul_zero]
theorem ae_smul_measure_le [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) :
    ae (c • μ) ≤ ae μ := fun _ h ↦ ae_smul_measure h c
section SMulWithZero
variable {R : Type*} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [NoZeroSMulDivisors R ℝ≥0∞] {c : R} {p : α → Prop}
lemma ae_smul_measure_iff (hc : c ≠ 0) {μ : Measure α} : (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by
  simp [ae_iff, hc]
@[simp] lemma ae_smul_measure_eq (hc : c ≠ 0) (μ : Measure α) : ae (c • μ) = ae μ := by
  ext; exact ae_smul_measure_iff hc
end SMulWithZero
theorem measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t := by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t ≤ μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ ≤ μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)
theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t := by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''
theorem measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : μ (toMeasurable (μ + ν) t ∩ s) = μ (t ∩ s) := by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1
theorem measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : ν (toMeasurable (μ + ν) t ∩ s) = ν (t ∩ s) := by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht
instance instPartialOrder {_ : MeasurableSpace α} : PartialOrder (Measure α) where
  le m₁ m₂ := ∀ s, m₁ s ≤ m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ s := le_trans (h₁ s) (h₂ s)
  le_antisymm _ _ h₁ h₂ := ext fun s _ => le_antisymm (h₁ s) (h₂ s)
theorem toOuterMeasure_le : μ₁.toOuterMeasure ≤ μ₂.toOuterMeasure ↔ μ₁ ≤ μ₂ := .rfl
theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s ≤ μ₂ s := outerMeasure_le_iff
theorem le_intro (h : ∀ s, MeasurableSet s → s.Nonempty → μ₁ s ≤ μ₂ s) : μ₁ ≤ μ₂ :=
  le_iff.2 fun s hs ↦ s.eq_empty_or_nonempty.elim (by rintro rfl; simp) (h s hs)
theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s := .rfl
theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, MeasurableSet s ∧ μ s < ν s :=
  lt_iff_le_not_le.trans <|
    and_congr Iff.rfl <| by simp only [le_iff, not_forall, not_le, exists_prop]
theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
  lt_iff_le_not_le.trans <| and_congr Iff.rfl <| by simp only [le_iff', not_forall, not_le]
instance instAddLeftMono {_ : MeasurableSpace α} : AddLeftMono (Measure α) :=
  ⟨fun _ν _μ₁ _μ₂ hμ s => add_le_add_left (hμ s) _⟩
protected theorem le_add_left (h : μ ≤ ν) : μ ≤ ν' + ν := fun s => le_add_left (h s)
protected theorem le_add_right (h : μ ≤ ν) : μ ≤ ν + ν' := fun s => le_add_right (h s)
section sInf
variable {m : Set (Measure α)}
theorem sInf_caratheodory (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet[(sInf (toOuterMeasure '' m)).caratheodory] s := by
  rw [OuterMeasure.sInf_eq_boundedBy_sInfGen]
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  simp only [OuterMeasure.sInfGen, le_iInf_iff, forall_mem_image, measure_eq_iInf t,
    coe_toOuterMeasure]
  intro μ hμ u htu _hu
  have hm : ∀ {s t}, s ⊆ t → OuterMeasure.sInfGen (toOuterMeasure '' m) s ≤ μ t := by
    intro s t hst
    rw [OuterMeasure.sInfGen_def, iInf_image]
    exact iInf₂_le_of_le μ hμ <| measure_mono hst
  rw [← measure_inter_add_diff u hs]
  exact add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| diff_subset_diff_left htu)
instance {_ : MeasurableSpace α} : InfSet (Measure α) :=
  ⟨fun m => (sInf (toOuterMeasure '' m)).toMeasure <| sInf_caratheodory⟩
theorem sInf_apply (hs : MeasurableSet s) : sInf m s = sInf (toOuterMeasure '' m) s :=
  toMeasure_apply _ _ hs
private theorem measure_sInf_le (h : μ ∈ m) : sInf m ≤ μ :=
  have : sInf (toOuterMeasure '' m) ≤ μ.toOuterMeasure := sInf_le (mem_image_of_mem _ h)
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s
private theorem measure_le_sInf (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ sInf m :=
  have : μ.toOuterMeasure ≤ sInf (toOuterMeasure '' m) :=
    le_sInf <| forall_mem_image.2 fun _ hμ ↦ toOuterMeasure_le.2 <| h _ hμ
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s
instance instCompleteSemilatticeInf {_ : MeasurableSpace α} : CompleteSemilatticeInf (Measure α) :=
  { (by infer_instance : PartialOrder (Measure α)),
    (by infer_instance : InfSet (Measure α)) with
    sInf_le := fun _s _a => measure_sInf_le
    le_sInf := fun _s _a => measure_le_sInf }
instance instCompleteLattice {_ : MeasurableSpace α} : CompleteLattice (Measure α) :=
  { completeLatticeOfCompleteSemilatticeInf (Measure α) with
    top :=
      { toOuterMeasure := ⊤,
        m_iUnion := by
          intro f _ _
          refine (measure_iUnion_le _).antisymm ?_
          if hne : (⋃ i, f i).Nonempty then
            rw [OuterMeasure.top_apply hne]
            exact le_top
          else
            simp_all [Set.not_nonempty_iff_eq_empty]
        trim_le := le_top },
    le_top := fun _ => toOuterMeasure_le.mp le_top
    bot := 0
    bot_le := fun _a _s => bot_le }
end sInf
lemma inf_apply {s : Set α} (hs : MeasurableSet s) :
    (μ ⊓ ν) s = sInf {m | ∃ t, m = μ (t ∩ s) + ν (tᶜ ∩ s)} := by
  rw [← sInf_pair, Measure.sInf_apply hs, OuterMeasure.sInf_apply
    (image_nonempty.2 <| insert_nonempty μ {ν})]
  refine le_antisymm (le_sInf fun m ⟨t, ht₁⟩ ↦ ?_) (le_iInf₂ fun t' ht' ↦ ?_)
  · subst ht₁
    set t' : ℕ → Set α := fun n ↦ if n = 0 then t ∩ s else if n = 1 then tᶜ ∩ s else ∅ with ht'
    refine (iInf₂_le t' fun x hx ↦ ?_).trans ?_
    · by_cases hxt : x ∈ t
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp [hx, hxt]
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp [hx, hxt]
    · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
      rw [tsum_eq_add_tsum_ite 0, tsum_eq_add_tsum_ite 1, if_neg zero_ne_one.symm,
        (tsum_eq_zero_iff ENNReal.summable).2 _, add_zero]
      · exact add_le_add (inf_le_left.trans <| by simp [ht']) (inf_le_right.trans <| by simp [ht'])
      · simp only [ite_eq_left_iff]
        intro n hn₁ hn₀
        simp only [ht', if_neg hn₀, if_neg hn₁, measure_empty, iInf_pair, le_refl, inf_of_le_left]
  · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
    set t := ⋃ n ∈ {k : ℕ | μ (t' k) ≤ ν (t' k)}, t' n with ht
    suffices hadd : μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n) by
      exact le_trans (sInf_le ⟨t, rfl⟩) hadd
    have hle₁ : μ (t ∩ s) ≤ ∑' (n : {k | μ (t' k) ≤ ν (t' k)}), μ (t' n) :=
      (measure_mono inter_subset_left).trans <| measure_biUnion_le _ (to_countable _) _
    have hcap : tᶜ ∩ s ⊆ ⋃ n ∈ {k | ν (t' k) < μ (t' k)}, t' n := by
      simp_rw [ht, compl_iUnion]
      refine fun x ⟨hx₁, hx₂⟩ ↦ mem_iUnion₂.2 ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 <| ht' hx₂
      refine ⟨i, ?_, hi⟩
      by_contra h
      simp only [mem_setOf_eq, not_lt] at h
      exact mem_iInter₂.1 hx₁ i h hi
    have hle₂ : ν (tᶜ ∩ s) ≤ ∑' (n : {k | ν (t' k) < μ (t' k)}), ν (t' n) :=
      (measure_mono hcap).trans (measure_biUnion_le ν (to_countable {k | ν (t' k) < μ (t' k)}) _)
    refine (add_le_add hle₁ hle₂).trans ?_
    have heq : {k | μ (t' k) ≤ ν (t' k)} ∪ {k | ν (t' k) < μ (t' k)} = univ := by
      ext k; simp [le_or_lt]
    conv in ∑' (n : ℕ), μ (t' n) ⊓ ν (t' n) => rw [← tsum_univ, ← heq]
    rw [tsum_union_disjoint (f := fun n ↦ μ (t' n) ⊓ ν (t' n)) ?_ ENNReal.summable ENNReal.summable]
    · refine add_le_add (tsum_congr ?_).le (tsum_congr ?_).le
      · rw [Subtype.forall]
        intro n hn; simpa
      · rw [Subtype.forall]
        intro n hn
        rw [mem_setOf_eq] at hn
        simp [le_of_lt hn]
    · rw [Set.disjoint_iff]
      rintro k ⟨hk₁, hk₂⟩
      rw [mem_setOf_eq] at hk₁ hk₂
      exact False.elim <| hk₂.not_le hk₁
@[simp]
theorem _root_.MeasureTheory.OuterMeasure.toMeasure_top :
    (⊤ : OuterMeasure α).toMeasure (by rw [OuterMeasure.top_caratheodory]; exact le_top) =
      (⊤ : Measure α) :=
  toOuterMeasure_toMeasure (μ := ⊤)
@[simp]
theorem toOuterMeasure_top {_ : MeasurableSpace α} :
    (⊤ : Measure α).toOuterMeasure = (⊤ : OuterMeasure α) :=
  rfl
@[simp]
theorem top_add : ⊤ + μ = ⊤ :=
  top_unique <| Measure.le_add_right le_rfl
@[simp]
theorem add_top : μ + ⊤ = ⊤ :=
  top_unique <| Measure.le_add_left le_rfl
protected theorem zero_le {_m0 : MeasurableSpace α} (μ : Measure α) : 0 ≤ μ :=
  bot_le
theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.le_iff_eq
@[simp]
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique fun s => (h ▸ measure_mono (subset_univ s) : μ s ≤ 0), fun h =>
    h.symm ▸ rfl⟩
theorem measure_univ_ne_zero : μ univ ≠ 0 ↔ μ ≠ 0 :=
  measure_univ_eq_zero.not
instance [NeZero μ] : NeZero (μ univ) := ⟨measure_univ_ne_zero.2 <| NeZero.ne μ⟩
@[simp]
theorem measure_univ_pos : 0 < μ univ ↔ μ ≠ 0 :=
  pos_iff_ne_zero.trans measure_univ_ne_zero
lemma nonempty_of_neZero (μ : Measure α) [NeZero μ] : Nonempty α :=
  (isEmpty_or_nonempty α).resolve_left fun h ↦ by
    simpa [eq_empty_of_isEmpty] using NeZero.ne (μ univ)
def liftLinear [MeasurableSpace β] (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) :
    Measure α →ₗ[ℝ≥0∞] Measure β where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      OuterMeasure.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [LinearMap.map_smulₛₗ, coe_smul, Pi.smul_apply,
      toMeasure_apply, smul_toOuterMeasure (R := ℝ≥0∞), OuterMeasure.coe_smul (R := ℝ≥0∞),
      smul_apply, hs]
lemma liftLinear_apply₀ {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : NullMeasurableSet s (liftLinear f hf μ)) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply₀ _ (hf μ) hs
@[simp]
theorem liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply _ (hf μ) hs
theorem le_liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) (s : Set β) :
    f μ.toOuterMeasure s ≤ liftLinear f hf μ s :=
  le_toMeasure_apply _ (hf μ) s
open Classical in
def mapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Measure α →ₗ[ℝ≥0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0
theorem mapₗ_congr {f g : α → β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    mapₗ f μ = mapₗ g μ := by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, liftLinear_apply, OuterMeasure.map_apply]
    using measure_congr (h.preimage s)
open Classical in
irreducible_def map [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (μ : Measure α) :
    Measure β :=
  if hf : AEMeasurable f μ then mapₗ (hf.mk f) μ else 0
theorem mapₗ_mk_apply_of_aemeasurable {f : α → β} (hf : AEMeasurable f μ) :
    mapₗ (hf.mk f) μ = map f μ := by simp [map, hf]
theorem mapₗ_apply_of_measurable {f : α → β} (hf : Measurable f) (μ : Measure α) :
    mapₗ f μ = map f μ := by
  simp only [← mapₗ_mk_apply_of_aemeasurable hf.aemeasurable]
  exact mapₗ_congr hf hf.aemeasurable.measurable_mk hf.aemeasurable.ae_eq_mk
@[simp]
theorem map_add (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    (μ + ν).map f = μ.map f + ν.map f := by simp [← mapₗ_apply_of_measurable hf]
@[simp]
theorem map_zero (f : α → β) : (0 : Measure α).map f = 0 := by
  by_cases hf : AEMeasurable f (0 : Measure α) <;> simp [map, hf]
@[simp]
theorem map_of_not_aemeasurable {f : α → β} {μ : Measure α} (hf : ¬AEMeasurable f μ) :
    μ.map f = 0 := by simp [map, hf]
theorem map_congr {f g : α → β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g μ := by
  by_cases hf : AEMeasurable f μ
  · have hg : AEMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AEMeasurable g μ := by simpa [← aemeasurable_congr h] using hf
    simp [map_of_not_aemeasurable, hf, hg]
@[simp]
protected theorem map_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (μ : Measure α) (f : α → β) : (c • μ).map f = c • μ.map f := by
  suffices ∀ c : ℝ≥0∞, (c • μ).map f = c • μ.map f by simpa using this (c • 1)
  clear c; intro c
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AEMeasurable f μ
  · have hfc : AEMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_smul_measure_iff hc).2 hf.ae_eq_mk⟩
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hfc,
      LinearMap.map_smulₛₗ, RingHom.id_apply]
    congr 1
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk
    exact EventuallyEq.trans ((ae_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk
  · have hfc : ¬AEMeasurable f (c • μ) := by
      intro hfc
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_smul_measure_iff hc).1 hfc.ae_eq_mk⟩
    simp [map_of_not_aemeasurable hf, map_of_not_aemeasurable hfc]
@[deprecated Measure.map_smul (since := "2024-11-13")]
protected theorem map_smul_nnreal (c : ℝ≥0) (μ : Measure α) (f : α → β) :
    (c • μ).map f = c • μ.map f :=
  μ.map_smul c f
variable {f : α → β}
lemma map_apply₀ {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹' s) := by
  rw [map, dif_pos hf, mapₗ, dif_pos hf.measurable_mk] at hs ⊢
  rw [liftLinear_apply₀ _ hs, measure_congr (hf.ae_eq_mk.preimage s)]
  rfl
@[simp]
theorem map_apply_of_aemeasurable (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) := map_apply₀ hf hs.nullMeasurableSet
@[simp]
theorem map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) :=
  map_apply_of_aemeasurable hf.aemeasurable hs
theorem map_toOuterMeasure (hf : AEMeasurable f μ) :
    (μ.map f).toOuterMeasure = (OuterMeasure.map f μ.toOuterMeasure).trim := by
  rw [← trimmed, OuterMeasure.trim_eq_trim_iff]
  intro s hs
  simp [hf, hs]
@[simp] lemma map_eq_zero_iff (hf : AEMeasurable f μ) : μ.map f = 0 ↔ μ = 0 := by
  simp_rw [← measure_univ_eq_zero, map_apply_of_aemeasurable hf .univ, preimage_univ]
@[simp] lemma mapₗ_eq_zero_iff (hf : Measurable f) : Measure.mapₗ f μ = 0 ↔ μ = 0 := by
  rw [mapₗ_apply_of_measurable hf, map_eq_zero_iff hf.aemeasurable]
lemma measure_preimage_of_map_eq_self {f : α → α} (hf : map f μ = μ)
    {s : Set α} (hs : NullMeasurableSet s μ) : μ (f ⁻¹' s) = μ s := by
  if hfm : AEMeasurable f μ then
    rw [← map_apply₀ hfm, hf]
    rwa [hf]
  else
    rw [map_of_not_aemeasurable hfm] at hf
    simp [← hf]
lemma map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f ≠ 0 ↔ μ ≠ 0 := (map_eq_zero_iff hf).not
lemma mapₗ_ne_zero_iff (hf : Measurable f) : Measure.mapₗ f μ ≠ 0 ↔ μ ≠ 0 :=
  (mapₗ_eq_zero_iff hf).not
@[simp]
theorem map_id : map id μ = μ :=
  ext fun _ => map_apply measurable_id
@[simp]
theorem map_id' : map (fun x => x) μ = μ :=
  map_id
theorem map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]
@[mono]
theorem map_mono {f : α → β} (h : μ ≤ ν) (hf : Measurable f) : μ.map f ≤ ν.map f :=
  le_iff.2 fun s hs ↦ by simp [hf.aemeasurable, hs, h _]
theorem le_map_apply {f : α → β} (hf : AEMeasurable f μ) (s : Set β) : μ (f ⁻¹' s) ≤ μ.map f s :=
  calc
    μ (f ⁻¹' s) ≤ μ (f ⁻¹' toMeasurable (μ.map f) s) := by gcongr; apply subset_toMeasurable
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aemeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _
theorem le_map_apply_image {f : α → β} (hf : AEMeasurable f μ) (s : Set α) :
    μ s ≤ μ.map f (f '' s) :=
  (measure_mono (subset_preimage_image f s)).trans (le_map_apply hf _)
theorem preimage_null_of_map_null {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
  nonpos_iff_eq_zero.mp <| (le_map_apply hf s).trans_eq hs
theorem tendsto_ae_map {f : α → β} (hf : AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f)) :=
  fun _ hs => preimage_null_of_map_null hf hs
section Sum
variable {f : ι → Measure α}
noncomputable def sum (f : ι → Measure α) : Measure α :=
  (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure <|
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)
theorem le_sum_apply (f : ι → Measure α) (s : Set α) : ∑' i, f i s ≤ sum f s :=
  le_toMeasure_apply _ _ _
@[simp]
theorem sum_apply (f : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    sum f s = ∑' i, f i s :=
  toMeasure_apply _ _ hs
theorem sum_apply₀ (f : ι → Measure α) {s : Set α} (hs : NullMeasurableSet s (sum f)) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, t_meas, ht⟩
  calc
  sum f s = sum f t := measure_congr ht.symm
  _ = ∑' i, f i t := sum_apply _ t_meas
  _ ≤ ∑' i, f i s := ENNReal.tsum_le_tsum fun i ↦ measure_mono ts
theorem sum_apply_of_countable [Countable ι] (f : ι → Measure α) (s : Set α) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq f s with ⟨t, hst, htm, ht⟩
  calc
  sum f s ≤ sum f t := measure_mono hst
  _ = ∑' i, f i t := sum_apply _ htm
  _ = ∑' i, f i s := by simp [ht]
theorem le_sum (μ : ι → Measure α) (i : ι) : μ i ≤ sum μ :=
  le_iff.2 fun s hs ↦ by simpa only [sum_apply μ hs] using ENNReal.le_tsum i
@[simp]
theorem sum_apply_eq_zero [Countable ι] {μ : ι → Measure α} {s : Set α} :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by
  simp [sum_apply_of_countable]
theorem sum_apply_eq_zero' {μ : ι → Measure α} {s : Set α} (hs : MeasurableSet s) :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by simp [hs]
@[simp] lemma sum_eq_zero : sum f = 0 ↔ ∀ i, f i = 0 := by
  simp +contextual [Measure.ext_iff, forall_swap (α := ι)]
@[simp]
lemma sum_zero : Measure.sum (fun (_ : ι) ↦ (0 : Measure α)) = 0 := by
  ext s hs
  simp [Measure.sum_apply _ hs]
theorem sum_sum {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum (fun (p : ι × ι') ↦ μ p.1 p.2) := by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']
theorem sum_comm {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m := by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]
theorem ae_sum_iff [Countable ι] {μ : ι → Measure α} {p : α → Prop} :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero
theorem ae_sum_iff' {μ : ι → Measure α} {p : α → Prop} (h : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero' h.compl
@[simp]
theorem sum_fintype [Fintype ι] (μ : ι → Measure α) : sum μ = ∑ i, μ i := by
  ext1 s hs
  simp only [sum_apply, finset_sum_apply, hs, tsum_fintype]
theorem sum_coe_finset (s : Finset ι) (μ : ι → Measure α) :
    (sum fun i : s => μ i) = ∑ i ∈ s, μ i := by rw [sum_fintype, Finset.sum_coe_sort s μ]
@[simp]
theorem ae_sum_eq [Countable ι] (μ : ι → Measure α) : ae (sum μ) = ⨆ i, ae (μ i) :=
  Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm
theorem sum_bool (f : Bool → Measure α) : sum f = f true + f false := by
  rw [sum_fintype, Fintype.sum_bool]
theorem sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν :=
  sum_bool _
@[simp]
theorem sum_of_isEmpty [IsEmpty ι] (μ : ι → Measure α) : sum μ = 0 := by
  rw [← measure_univ_eq_zero, sum_apply _ MeasurableSet.univ, tsum_empty]
@[deprecated (since := "2024-06-11")] alias sum_of_empty := sum_of_isEmpty
theorem sum_add_sum_compl (s : Set ι) (μ : ι → Measure α) :
    ((sum fun i : s => μ i) + sum fun i : ↥sᶜ => μ i) = sum μ := by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable ENNReal.summable
theorem sum_congr {μ ν : ℕ → Measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
  congr_arg sum (funext h)
theorem sum_add_sum {ι : Type*} (μ ν : ι → Measure α) : sum μ + sum ν = sum fun n => μ n + ν n := by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs, Pi.add_apply, coe_add,
    tsum_add ENNReal.summable ENNReal.summable]
@[simp] lemma sum_comp_equiv {ι ι' : Type*} (e : ι' ≃ ι) (m : ι → Measure α) :
    sum (m ∘ e) = sum m := by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n ↦ m n s)
@[simp] lemma sum_extend_zero {ι ι' : Type*} {f : ι → ι'} (hf : Injective f) (m : ι → Measure α) :
    sum (Function.extend f m 0) = sum m := by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α ↦ μ s)]
end Sum
def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0
@[inherit_doc MeasureTheory.Measure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous
theorem absolutelyContinuous_of_le (h : μ ≤ ν) : μ ≪ ν := fun s hs =>
  nonpos_iff_eq_zero.1 <| hs ▸ le_iff'.1 h s
alias _root_.LE.le.absolutelyContinuous := absolutelyContinuous_of_le
theorem absolutelyContinuous_of_eq (h : μ = ν) : μ ≪ ν :=
  h.le.absolutelyContinuous
alias _root_.Eq.absolutelyContinuous := absolutelyContinuous_of_eq
namespace AbsolutelyContinuous
theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → ν s = 0 → μ s = 0) : μ ≪ ν := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)
@[refl]
protected theorem refl {_m0 : MeasurableSpace α} (μ : Measure α) : μ ≪ μ :=
  rfl.absolutelyContinuous
protected theorem rfl : μ ≪ μ := fun _s hs => hs
instance instIsRefl {_ : MeasurableSpace α} : IsRefl (Measure α) (· ≪ ·) :=
  ⟨fun _ => AbsolutelyContinuous.rfl⟩
@[simp]
protected lemma zero (μ : Measure α) : 0 ≪ μ := fun _ _ ↦ by simp
@[trans]
protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ := fun _s hs => h1 <| h2 hs
@[mono]
protected theorem map (h : μ ≪ ν) {f : α → β} (hf : Measurable f) : μ.map f ≪ ν.map f :=
  AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _
protected theorem smul_left [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ ν := fun s hνs => by
  simp only [h hνs, smul_apply, smul_zero, ← smul_one_smul ℝ≥0∞ c (0 : ℝ≥0∞)]
protected theorem smul [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ c • ν := by
  intro s hνs
  rw [smul_apply, ← smul_one_smul ℝ≥0∞, smul_eq_mul, mul_eq_zero] at hνs ⊢
  exact hνs.imp_right fun hs ↦ h hs
@[deprecated (since := "2024-11-14")] protected alias smul_both := AbsolutelyContinuous.smul
protected lemma add (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν') : μ₁ + μ₂ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩
lemma add_left_iff {μ₁ μ₂ ν : Measure α} :
    μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.1.add h.2).trans ?_⟩
  · have : ∀ s, ν s = 0 → μ₁ s = 0 ∧ μ₂ s = 0 := by intro s hs0; simpa using h hs0
    exact ⟨fun s hs0 ↦ (this s hs0).1, fun s hs0 ↦ (this s hs0).2⟩
  · rw [← two_smul ℝ≥0]
    exact AbsolutelyContinuous.rfl.smul_left 2
lemma add_left {μ₁ μ₂ ν : Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) : μ₁ + μ₂ ≪ ν :=
  Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩
lemma add_right (h1 : μ ≪ ν) (ν' : Measure α) : μ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1
end AbsolutelyContinuous
@[simp]
lemma absolutelyContinuous_zero_iff : μ ≪ 0 ↔ μ = 0 :=
  ⟨fun h ↦ measure_univ_eq_zero.mp (h rfl), fun h ↦ h.symm ▸ AbsolutelyContinuous.zero _⟩
alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl
lemma absolutelyContinuous_sum_left {μs : ι → Measure α} (hμs : ∀ i, μs i ≪ ν) :
    Measure.sum μs ≪ ν :=
  AbsolutelyContinuous.mk fun s hs hs0 ↦ by simp [sum_apply _ hs, fun i ↦ hμs i hs0]
lemma absolutelyContinuous_sum_right {μs : ι → Measure α} (i : ι) (hνμ : ν ≪ μs i) :
    ν ≪ Measure.sum μs := by
  refine AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)
lemma smul_absolutelyContinuous {c : ℝ≥0∞} : c • μ ≪ μ := .smul_left .rfl _
theorem absolutelyContinuous_of_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hμ'_le : μ' ≤ c • μ) :
    μ' ≪ μ :=
  (Measure.absolutelyContinuous_of_le hμ'_le).trans smul_absolutelyContinuous
lemma absolutelyContinuous_smul {c : ℝ≥0∞} (hc : c ≠ 0) : μ ≪ c • μ := by
  simp [AbsolutelyContinuous, hc]
theorem ae_le_iff_absolutelyContinuous : ae μ ≤ ae ν ↔ μ ≪ ν :=
  ⟨fun h s => by
    rw [measure_zero_iff_ae_nmem, measure_zero_iff_ae_nmem]
    exact fun hs => h hs, fun h _ hs => h hs⟩
alias ⟨_root_.LE.le.absolutelyContinuous_of_ae, AbsolutelyContinuous.ae_le⟩ :=
  ae_le_iff_absolutelyContinuous
alias ae_mono' := AbsolutelyContinuous.ae_le
theorem AbsolutelyContinuous.ae_eq (h : μ ≪ ν) {f g : α → δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
  h.ae_le h'
protected theorem _root_.MeasureTheory.AEDisjoint.of_absolutelyContinuous
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≪ μ) :
    AEDisjoint ν s t := h' h
protected theorem _root_.MeasureTheory.AEDisjoint.of_le
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≤ μ) :
    AEDisjoint ν s t :=
  h.of_absolutelyContinuous (Measure.absolutelyContinuous_of_le h')
structure QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α → β)
  (μa : Measure α := by volume_tac)
  (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected absolutelyContinuous : μa.map f ≪ μb
namespace QuasiMeasurePreserving
protected theorem id {_m0 : MeasurableSpace α} (μ : Measure α) : QuasiMeasurePreserving id μ μ :=
  ⟨measurable_id, map_id.absolutelyContinuous⟩
variable {μa μa' : Measure α} {μb μb' : Measure β} {μc : Measure γ} {f : α → β}
protected theorem _root_.Measurable.quasiMeasurePreserving
    {_m0 : MeasurableSpace α} (hf : Measurable f) (μ : Measure α) :
    QuasiMeasurePreserving f μ (μ.map f) :=
  ⟨hf, AbsolutelyContinuous.rfl⟩
theorem mono_left (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) :
    QuasiMeasurePreserving f μa' μb :=
  ⟨h.1, (ha.map h.1).trans h.2⟩
theorem mono_right (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') :
    QuasiMeasurePreserving f μa μb' :=
  ⟨h.1, h.2.trans ha⟩
@[mono]
theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa' μb' :=
  (h.mono_left ha).mono_right hb
protected theorem comp {g : β → γ} {f : α → β} (hg : QuasiMeasurePreserving g μb μc)
    (hf : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.measurable.comp hf.measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩
protected theorem iterate {f : α → α} (hf : QuasiMeasurePreserving f μa μa) :
    ∀ n, QuasiMeasurePreserving f^[n] μa μa
  | 0 => QuasiMeasurePreserving.id μa
  | n + 1 => (hf.iterate n).comp hf
protected theorem aemeasurable (hf : QuasiMeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable
theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : QuasiMeasurePreserving f μa μb) (c : R) : QuasiMeasurePreserving f (c • μa) (c • μb) :=
  ⟨hf.1, by rw [Measure.map_smul]; exact hf.2.smul c⟩
theorem ae_map_le (h : QuasiMeasurePreserving f μa μb) : ae (μa.map f) ≤ ae μb :=
  h.2.ae_le
theorem tendsto_ae (h : QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb) :=
  (tendsto_ae_map h.aemeasurable).mono_right h.ae_map_le
theorem ae (h : QuasiMeasurePreserving f μa μb) {p : β → Prop} (hg : ∀ᵐ x ∂μb, p x) :
    ∀ᵐ x ∂μa, p (f x) :=
  h.tendsto_ae hg
theorem ae_eq (h : QuasiMeasurePreserving f μa μb) {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) :
    g₁ ∘ f =ᵐ[μa] g₂ ∘ f :=
  h.ae hg
theorem preimage_null (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) :
    μa (f ⁻¹' s) = 0 :=
  preimage_null_of_map_null h.aemeasurable (h.2 hs)
theorem preimage_mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s ≤ᵐ[μb] t) :
    f ⁻¹' s ≤ᵐ[μa] f ⁻¹' t :=
  eventually_map.mp <|
    Eventually.filter_mono (tendsto_ae_map hf.aemeasurable) (Eventually.filter_mono hf.ae_map_le h)
theorem preimage_ae_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) :
    f ⁻¹' s =ᵐ[μa] f ⁻¹' t :=
  EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)
theorem _root_.MeasureTheory.NullMeasurableSet.preimage {s : Set β} (hs : NullMeasurableSet s μb)
    (hf : QuasiMeasurePreserving f μa μb) : NullMeasurableSet (f ⁻¹' s) μa :=
  let ⟨t, htm, hst⟩ := hs
  ⟨f ⁻¹' t, hf.measurable htm, hf.preimage_ae_eq hst⟩
theorem preimage_iterate_ae_eq {s : Set α} {f : α → α} (hf : QuasiMeasurePreserving f μ μ) (k : ℕ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s := by
  induction' k with k ih; · rfl
  rw [iterate_succ, preimage_comp]
  exact EventuallyEq.trans (hf.preimage_ae_eq ih) hs
theorem image_zpow_ae_eq {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ μ)
    (he' : QuasiMeasurePreserving e.symm μ μ) (k : ℤ) (hs : e '' s =ᵐ[μ] s) :
    (⇑(e ^ k)) '' s =ᵐ[μ] s := by
  rw [Equiv.image_eq_preimage]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · replace hs : (⇑e⁻¹) ⁻¹' s =ᵐ[μ] s := by rwa [Equiv.image_eq_preimage] at hs
    replace he' : (⇑e⁻¹)^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_natCast]
    replace hs : e ⁻¹' s =ᵐ[μ] s := by
      convert he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : (⇑e)^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he
theorem limsup_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : limsup (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n ↦ by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs
theorem liminf_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : liminf (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  liminf_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n ↦ by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs
theorem exists_preimage_eq_of_preimage_ae {f : α → α} (h : QuasiMeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set α, MeasurableSet t ∧ t =ᵐ[μ] s ∧ f ⁻¹' t = t := by
  obtain ⟨t, htm, ht⟩ := hs
  refine ⟨limsup (f^[·] ⁻¹' t) atTop, ?_, ?_, ?_⟩
  · exact .measurableSet_limsup fun n ↦ h.measurable.iterate n htm
  · have : f ⁻¹' t =ᵐ[μ] t := (h.preimage_ae_eq ht.symm).trans (hs'.trans ht)
    exact limsup_ae_eq_of_forall_ae_eq _ fun n ↦ .trans (h.preimage_iterate_ae_eq _ this) ht.symm
  · simp only [Set.preimage_iterate_eq]
    exact CompleteLatticeHom.apply_limsup_iterate (CompleteLatticeHom.setPreimage f) t
open Pointwise
@[to_additive]
theorem smul_ae_eq_of_ae_eq {G α : Type*} [Group G] [MulAction G α] {_ : MeasurableSpace α}
    {s t : Set α} {μ : Measure α} (g : G)
    (h_qmp : QuasiMeasurePreserving (g⁻¹ • · : α → α) μ μ)
    (h_ae_eq : s =ᵐ[μ] t) : (g • s : Set α) =ᵐ[μ] (g • t : Set α) := by
  simpa only [← preimage_smul_inv] using h_qmp.ae_eq h_ae_eq
end QuasiMeasurePreserving
section Pointwise
open Pointwise
@[to_additive]
theorem pairwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [MulAction G α]
    {_ : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (h_ae_disjoint : ∀ g ≠ (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving (g • ·) μ μ) :
    Pairwise (AEDisjoint μ on fun g : G => g • s) := by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g ≠ 1 := by
    rw [Ne, inv_mul_eq_one]
    exact hg.symm
  have : (g₂⁻¹ • ·) ⁻¹' (g • s ∩ s) = g₁ • s ∩ g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹), image_smul, smul_set_inter, smul_smul,
      smul_smul, inv_mul_cancel, one_smul]
  change μ (g₁ • s ∩ g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)
end Pointwise
def cofinite {m0 : MeasurableSpace α} (μ : Measure α) : Filter α :=
  comk (μ · < ∞) (by simp) (fun _ ht _ hs ↦ (measure_mono hs).trans_lt ht) fun s hs t ht ↦
    (measure_union_le s t).trans_lt <| ENNReal.add_lt_top.2 ⟨hs, ht⟩
theorem mem_cofinite : s ∈ μ.cofinite ↔ μ sᶜ < ∞ :=
  Iff.rfl
theorem compl_mem_cofinite : sᶜ ∈ μ.cofinite ↔ μ s < ∞ := by rw [mem_cofinite, compl_compl]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞ :=
  Iff.rfl
instance cofinite.instIsMeasurablyGenerated : IsMeasurablyGenerated μ.cofinite where
  exists_measurable_subset s hs := by
    refine ⟨(toMeasurable μ sᶜ)ᶜ, ?_, (measurableSet_toMeasurable _ _).compl, ?_⟩
    · rwa [compl_mem_cofinite, measure_toMeasurable]
    · rw [compl_subset_comm]
      apply subset_toMeasurable
end Measure
open Measure
open MeasureTheory
protected theorem _root_.AEMeasurable.nullMeasurable {f : α → β} (h : AEMeasurable f μ) :
    NullMeasurable f μ :=
  let ⟨_g, hgm, hg⟩ := h; hgm.nullMeasurable.congr hg.symm
lemma _root_.AEMeasurable.nullMeasurableSet_preimage {f : α → β} {s : Set β}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) : NullMeasurableSet (f ⁻¹' s) μ :=
  hf.nullMeasurable hs
theorem NullMeasurableSet.mono_ac (h : NullMeasurableSet s μ) (hle : ν ≪ μ) :
    NullMeasurableSet s ν :=
  h.preimage <| (QuasiMeasurePreserving.id μ).mono_left hle
theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (hle : ν ≤ μ) : NullMeasurableSet s ν :=
  h.mono_ac hle.absolutelyContinuous
theorem AEDisjoint.preimage {ν : Measure β} {f : α → β} {s t : Set β} (ht : AEDisjoint ν s t)
    (hf : QuasiMeasurePreserving f μ ν) : AEDisjoint μ (f ⁻¹' s) (f ⁻¹' t) :=
  hf.preimage_null ht
@[simp]
theorem ae_eq_bot : ae μ = ⊥ ↔ μ = 0 := by
  rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]
@[simp]
theorem ae_neBot : (ae μ).NeBot ↔ μ ≠ 0 :=
  neBot_iff.trans (not_congr ae_eq_bot)
instance Measure.ae.neBot [NeZero μ] : (ae μ).NeBot := ae_neBot.2 <| NeZero.ne μ
@[simp]
theorem ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measure α) = ⊥ :=
  ae_eq_bot.2 rfl
@[mono]
theorem ae_mono (h : μ ≤ ν) : ae μ ≤ ae ν :=
  h.absolutelyContinuous.ae_le
theorem mem_ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    s ∈ ae (μ.map f) ↔ f ⁻¹' s ∈ ae μ := by
  simp only [mem_ae_iff, map_apply_of_aemeasurable hf hs.compl, preimage_compl]
theorem mem_ae_of_mem_ae_map {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : s ∈ ae (μ.map f)) : f ⁻¹' s ∈ ae μ :=
  (tendsto_ae_map hf).eventually hs
theorem ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop}
    (hp : MeasurableSet { x | p x }) : (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_map_iff hf hp
theorem ae_of_ae_map {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop} (h : ∀ᵐ y ∂μ.map f, p y) :
    ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_of_mem_ae_map hf h
theorem ae_map_mem_range {m0 : MeasurableSpace α} (f : α → β) (hf : MeasurableSet (range f))
    (μ : Measure α) : ∀ᵐ x ∂μ.map f, x ∈ range f := by
  by_cases h : AEMeasurable f μ
  · change range f ∈ ae (μ.map f)
    rw [mem_ae_map_iff h hf]
    filter_upwards using mem_range_self
  · simp [map_of_not_aemeasurable h]
section Intervals
theorem biSup_measure_Iic [Preorder α] {s : Set α} (hsc : s.Countable)
    (hst : ∀ x : α, ∃ y ∈ s, x ≤ y) (hdir : DirectedOn (· ≤ ·) s) :
    ⨆ x ∈ s, μ (Iic x) = μ univ := by
  rw [← measure_biUnion_eq_iSup hsc]
  · congr
    simp only [← bex_def] at hst
    exact iUnion₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_val.mono_comp _ fun x y => Iic_subset_Iic.2)
theorem tendsto_measure_Ico_atTop [Preorder α] [NoMaxOrder α]
    [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ico a x)) atTop (𝓝 (μ (Ici a))) := by
  rw [← iUnion_Ico_right]
  exact tendsto_measure_iUnion_atTop (antitone_const.Ico monotone_id)
theorem tendsto_measure_Ioc_atBot [Preorder α] [NoMinOrder α]
    [(atBot : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioc x a)) atBot (𝓝 (μ (Iic a))) := by
  rw [← iUnion_Ioc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioc antitone_const)
theorem tendsto_measure_Iic_atTop [Preorder α] [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Iic x)) atTop (𝓝 (μ univ)) := by
  rw [← iUnion_Iic]
  exact tendsto_measure_iUnion_atTop monotone_Iic
theorem tendsto_measure_Ici_atBot [Preorder α] [(atBot : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Ici x)) atBot (𝓝 (μ univ)) :=
  tendsto_measure_Iic_atTop (α := αᵒᵈ) μ
variable [PartialOrder α] {a b : α}
theorem Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a := by
  rw [← Iic_diff_right, diff_ae_eq_self, measure_mono_null Set.inter_subset_right ha]
theorem Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a :=
  Iio_ae_eq_Iic' (α := αᵒᵈ) ha
theorem Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)
theorem Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)
theorem Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)
theorem Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)
theorem Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)
theorem Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b :=
  (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)
end Intervals
end
end MeasureTheory
namespace MeasurableEmbedding
open MeasureTheory Measure
variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} {μ ν : Measure α}
nonrec theorem map_apply (hf : MeasurableEmbedding f) (μ : Measure α) (s : Set β) :
    μ.map f s = μ (f ⁻¹' s) := by
  refine le_antisymm ?_ (le_map_apply hf.measurable.aemeasurable s)
  set t := f '' toMeasurable μ (f ⁻¹' s) ∪ (range f)ᶜ
  have htm : MeasurableSet t :=
    (hf.measurableSet_image.2 <| measurableSet_toMeasurable _ _).union
      hf.measurableSet_range.compl
  have hst : s ⊆ t := by
    rw [subset_union_compl_iff_inter_subset, ← image_preimage_eq_inter_range]
    exact image_subset _ (subset_toMeasurable _ _)
  have hft : f ⁻¹' t = toMeasurable μ (f ⁻¹' s) := by
    rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      hf.injective.preimage_image]
  calc
    μ.map f s ≤ μ.map f t := by gcongr
    _ = μ (f ⁻¹' s) := by rw [map_apply hf.measurable htm, hft, measure_toMeasurable]
lemma absolutelyContinuous_map (hf : MeasurableEmbedding f) (hμν : μ ≪ ν) :
    μ.map f ≪ ν.map f := by
  intro t ht
  rw [hf.map_apply] at ht ⊢
  exact hμν ht
end MeasurableEmbedding
namespace MeasurableEquiv
open Equiv MeasureTheory.Measure
variable {_ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
protected theorem map_apply (f : α ≃ᵐ β) (s : Set β) : μ.map f s = μ (f ⁻¹' s) :=
  f.measurableEmbedding.map_apply _ _
@[simp]
theorem map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm = μ := by
  simp [map_map e.symm.measurable e.measurable]
@[simp]
theorem map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e = ν := by
  simp [map_map e.measurable e.symm.measurable]
theorem map_measurableEquiv_injective (e : α ≃ᵐ β) : Injective (Measure.map e) := by
  intro μ₁ μ₂ hμ
  apply_fun Measure.map e.symm at hμ
  simpa [map_symm_map e] using hμ
theorem map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ ν.map e.symm = μ := by
  rw [← (map_measurableEquiv_injective e).eq_iff, map_map_symm, eq_comm]
theorem map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map f (ae μ) = ae (map f μ) := by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]
theorem quasiMeasurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    QuasiMeasurePreserving e.symm (map e μ) μ :=
  ⟨e.symm.measurable, by rw [Measure.map_map, e.symm_comp_self, Measure.map_id] <;> measurability⟩
end MeasurableEquiv
end
set_option linter.style.longFile 2100