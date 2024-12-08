import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace MeasureTheory
section LimsupClosedLEAndLELiminfOpen
variable {Ω : Type*} [MeasurableSpace Ω]
theorem le_measure_compl_liminf_of_limsup_measure_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i ↦ μs i E) ≤ μ E) :
    μ Eᶜ ≤ L.liminf fun i ↦ μs i Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.liminf fun i : ι ↦ 1 - μs i E) = L.liminf ((fun x ↦ 1 - x) ∘ fun i : ι ↦ μs i E)
      from rfl]
  have key := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i ↦ μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h
theorem le_measure_liminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i ↦ μs i Eᶜ) ≤ μ Eᶜ) :
    μ E ≤ L.liminf fun i ↦ μs i E :=
  compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h
theorem limsup_measure_compl_le_of_le_liminf_measure {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ E ≤ L.liminf fun i ↦ μs i E) :
    (L.limsup fun i ↦ μs i Eᶜ) ≤ μ Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.limsup fun i : ι ↦ 1 - μs i E) = L.limsup ((fun x ↦ 1 - x) ∘ fun i : ι ↦ μs i E)
      from rfl]
  have key := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i ↦ μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h
theorem limsup_measure_le_of_le_liminf_measure_compl {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ Eᶜ ≤ L.liminf fun i ↦ μs i Eᶜ) :
    (L.limsup fun i ↦ μs i E) ≤ μ E :=
  compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h
variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
theorem limsup_measure_closed_le_iff_liminf_measure_open_ge {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μs i)] :
    (∀ F, IsClosed F → (L.limsup fun i ↦ μs i F) ≤ μ F) ↔
      ∀ G, IsOpen G → μ G ≤ L.liminf fun i ↦ μs i G := by
  constructor
  · intro h G G_open
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))
end LimsupClosedLEAndLELiminfOpen 
section TendstoOfNullFrontier
variable {Ω : Type*} [MeasurableSpace Ω]
theorem tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} {E₀ E E₁ : Set Ω} (E₀_subset : E₀ ⊆ E) (subset_E₁ : E ⊆ E₁)
    (nulldiff : μ (E₁ \ E₀) = 0) (h_E₀ : μ E₀ ≤ L.liminf fun i ↦ μs i E₀)
    (h_E₁ : (L.limsup fun i ↦ μs i E₁) ≤ μ E₁) : L.Tendsto (fun i ↦ μs i E) (𝓝 (μ E)) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      EventuallyLE.antisymm E₀_subset.eventuallyLE
        (subset_E₁.eventuallyLE.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ ≤ L.liminf fun i ↦ μs i E₀ := h_E₀
      _ ≤ L.liminf fun i ↦ μs i E :=
        liminf_le_liminf (.of_forall fun _ ↦ measure_mono E₀_subset)
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      EventuallyLE.antisymm subset_E₁.eventuallyLE
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventuallyLE)
    calc
      (L.limsup fun i ↦ μs i E) ≤ L.limsup fun i ↦ μs i E₁ :=
        limsup_le_limsup (.of_forall fun _ ↦ measure_mono subset_E₁)
      _ ≤ μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
  · infer_param
  · infer_param
variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
theorem tendsto_measure_of_null_frontier {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)]
    (h_opens : ∀ G, IsOpen G → μ G ≤ L.liminf fun i ↦ μs i G) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : L.Tendsto (fun i ↦ μs i E) (𝓝 (μ E)) :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ μs i F) ≤ μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ isOpen_interior) (h_closeds _ isClosed_closure)
end TendstoOfNullFrontier 
section ConvergenceImpliesLimsupClosedLE
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω}
    {μs : ι → FiniteMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos _
  have ε_pos' := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr ε_pos.ne.symm)).ne.symm
  let fs := F_closed.apprSeq
  have key₁ : Tendsto (fun n ↦ ∫⁻  ω, (fs n ω : ℝ≥0∞) ∂μ) atTop (𝓝 ((μ : Measure Ω) F)) :=
    HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed (μ : Measure Ω)
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 :=
    ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne ε_pos'
  obtain ⟨M, hM⟩ := eventually_atTop.mp <| key₁.eventually_lt_const room₁
  have key₂ := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (fs M)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a ↦ fs M a) <
      (lintegral (μ : Measure Ω) fun a ↦ fs M a) + ε / 2 :=
    ENNReal.lt_add_right (ne_of_lt ((fs M).lintegral_lt_top_of_nnreal _)) ε_pos'
  have ev_near := key₂.eventually_le_const room₂
  have ev_near' := ev_near.mono
    (fun n ↦ le_trans (HasOuterApproxClosed.measure_le_lintegral F_closed (μs n) M))
  apply (Filter.limsup_le_limsup ev_near').trans
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : ℝ≥0∞)))
  simp only [add_assoc, ENNReal.add_halves, le_refl]
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i ↦ (μs i : Measure Ω) G :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i ↦ (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F :=
    fun _ F_closed ↦ limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  haveI h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ L.liminf fun i ↦ (μs i : Measure Ω) G :=
    fun _ G_open ↦ le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (E_nullbdry : μ (frontier E) = 0) : Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)) := by
  have key := tendsto_measure_of_null_frontier_of_tendsto' μs_lim (by simpa using E_nullbdry)
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key
end ConvergenceImpliesLimsupClosedLE 
section LimitBorelImpliesLimsupClosedLE
open ENNReal
variable {Ω : Type*} [PseudoEMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
theorem exists_null_frontier_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : ℝ}
    (hab : a < b) : ∃ r ∈ Ioo a b, μ (frontier (Metric.thickening r s)) = 0 := by
  have mbles : ∀ r : ℝ, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r ↦ isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) mbles disjs
  have aux := measure_diff_null (s := Ioo a b) (Set.Countable.measure_zero key volume)
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  rw [← Real.volume_Ioo, ← aux] at len_pos
  rcases nonempty_of_measure_ne_zero len_pos.ne.symm with ⟨r, ⟨r_in_Ioo, hr⟩⟩
  refine ⟨r, r_in_Ioo, ?_⟩
  simpa only [mem_setOf_eq, not_lt, le_zero_iff] using hr
theorem exists_null_frontiers_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) :
    ∃ rs : ℕ → ℝ,
      Tendsto rs atTop (𝓝 0) ∧ ∀ n, 0 < rs n ∧ μ (frontier (Metric.thickening (rs n) s)) = 0 := by
  rcases exists_seq_strictAnti_tendsto (0 : ℝ) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  have obs := fun n : ℕ => exists_null_frontier_thickening μ s (Rs_pos n)
  refine ⟨fun n : ℕ => (obs n).choose, ⟨?_, ?_⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n ↦ (obs n).choose_spec.1.1.le) fun n ↦ (obs n).choose_spec.1.2.le
  · exact fun n ↦ ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩
lemma limsup_measure_closed_le_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ι → Measure Ω}
    (h : ∀ {E : Set Ω}, MeasurableSet E → μ (frontier E) = 0 →
            Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (F : Set Ω) (F_closed : IsClosed F) :
    L.limsup (fun i ↦ μs i F) ≤ μ F := by
  rcases L.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', zero_le]
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : ∀ n, 0 < rs n := fun n ↦ ((Classical.choose_spec ex).2 n).1
  have rs_null : ∀ n, μ (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n ↦ ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : ∀ n, IsOpen (Metric.thickening (rs n) F) :=
    fun n ↦ Metric.isOpen_thickening
  have key := fun (n : ℕ) ↦ h (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intros ε ε_pos μF_finite
  have keyB := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := F)
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhd : Iio (μ F + ε) ∈ 𝓝 (μ F) :=
    Iio_mem_nhds <| ENNReal.lt_add_right μF_finite.ne (ENNReal.coe_pos.mpr ε_pos).ne'
  specialize rs_lim (keyB nhd)
  simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux : (fun i ↦ (μs i F)) ≤ᶠ[L] (fun i ↦ μs i (Metric.thickening (rs m) F)) :=
    .of_forall <| fun i ↦ measure_mono (Metric.self_subset_thickening (rs_pos m) F)
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le
lemma le_liminf_measure_open_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ {E}, MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (G : Set Ω) (G_open : IsOpen G) :
    μ G ≤ L.liminf (fun i ↦ μs i G) := by
  apply le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
  exact limsup_measure_closed_le_of_forall_tendsto_measure h _ (isClosed_compl_iff.mpr G_open)
end LimitBorelImpliesLimsupClosedLE 
section le_liminf_open_implies_convergence
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) f_cont.aemeasurable]
  calc  ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) := ?_ 
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) := ?_ 
  · 
    exact (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans
            (le_refl _)
  · 
    exact lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))
lemma integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  have same := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
                  f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (Eventually.of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert ENNReal.toReal_mono ?_ same
  · simp only [fun i ↦ @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (Eventually.of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : ∀ i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) ≤ nndist 0 g := fun i ↦ by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply ENNReal.liminf_toReal_eq ENNReal.coe_ne_top (Eventually.of_forall bound)
  · apply ne_of_lt
    have obs := fun (i : ℕ) ↦ @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) ℝ _ f
    simp only [measure_univ, mul_one] at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : ℝ≥0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, .of_forall (by simp only [ge_iff_le, zero_le, forall_const])⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_to_continuous_fun] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm
theorem tendsto_of_forall_isOpen_le_liminf {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω}
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  apply tendsto_integral_of_forall_integral_le_liminf_integral
  intro f f_nn
  apply integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure (f := f) f_nn
  intro G G_open
  specialize h_opens G G_open
  have aux : ENNReal.ofNNReal (liminf (fun i ↦ μs i G) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun i ↦ μs i G) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · exact ENNReal.continuous_coe.continuousAt
    · exact IsBoundedUnder.isCoboundedUnder_ge ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h_opens
  simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert obs
  simp only [Function.comp_apply, ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
end le_liminf_open_implies_convergence
end MeasureTheory 