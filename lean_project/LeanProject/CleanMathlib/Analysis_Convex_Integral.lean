import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Average
open MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function
open scoped Topology ENNReal Convex
variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {s : Set E} {t : Set α} {f : α → E} {g : E → ℝ} {C : ℝ}
theorem Convex.integral_mem [IsProbabilityMeasure μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hf : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (∫ x, f x ∂μ) ∈ s := by
  borelize E
  rcases hfi.aestronglyMeasurable with ⟨g, hgm, hfg⟩
  haveI : SeparableSpace (range g ∩ s : Set E) :=
    (hgm.isSeparable_range.mono inter_subset_left).separableSpace
  obtain ⟨y₀, h₀⟩ : (range g ∩ s).Nonempty := by
    rcases (hf.and hfg).exists with ⟨x₀, h₀⟩
    exact ⟨f x₀, by simp only [h₀.2, mem_range_self], h₀.1⟩
  rw [integral_congr_ae hfg]; rw [integrable_congr hfg] at hfi
  have hg : ∀ᵐ x ∂μ, g x ∈ closure (range g ∩ s) := by
    filter_upwards [hfg.rw (fun _ y => y ∈ s) hf] with x hx
    apply subset_closure
    exact ⟨mem_range_self _, hx⟩
  set G : ℕ → SimpleFunc α E := SimpleFunc.approxOn _ hgm.measurable (range g ∩ s) y₀ h₀
  have : Tendsto (fun n => (G n).integral μ) atTop (𝓝 <| ∫ x, g x ∂μ) :=
    tendsto_integral_approxOn_of_measurable hfi _ hg _ (integrable_const _)
  refine hsc.mem_of_tendsto this (Eventually.of_forall fun n => hs.sum_mem ?_ ?_ ?_)
  · exact fun _ _ => ENNReal.toReal_nonneg
  · rw [← ENNReal.toReal_sum, (G n).sum_range_measure_preimage_singleton, measure_univ,
      ENNReal.one_toReal]
    exact fun _ _ => measure_ne_top _ _
  · simp only [SimpleFunc.mem_range, forall_mem_range]
    intro x
    apply (range g).inter_subset_right
    exact SimpleFunc.approxOn_mem hgm.measurable h₀ _ _
theorem Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (⨍ x, f x ∂μ) ∈ s :=
  hs.integral_mem hsc (ae_mono' smul_absolutelyContinuous hfs) hfi.to_average
theorem Convex.set_average_mem (hs : Convex ℝ s) (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) : (⨍ x in t, f x ∂μ) ∈ s :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hs.average_mem hsc hfs hfi
theorem Convex.set_average_mem_closure (hs : Convex ℝ s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) :
    (⨍ x in t, f x ∂μ) ∈ closure s :=
  hs.closure.set_average_mem isClosed_closure h0 ht (hfs.mono fun _ hx => subset_closure hx) hfi
theorem ConvexOn.average_mem_epigraph [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  have ht_mem : ∀ᵐ x ∂μ, (f x, g (f x)) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
    hfs.mono fun x hx => ⟨hx, le_rfl⟩
  exact average_pair hfi hgi ▸
    hg.convex_epigraph.average_mem (hsc.epigraph hgc) ht_mem (hfi.prod_mk hgi)
theorem ConcaveOn.average_mem_hypograph [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa only [mem_setOf_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.average_mem_epigraph hgc.neg hsc hfs hfi hgi.neg
theorem ConvexOn.map_average_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ :=
  (hg.average_mem_epigraph hgc hsc hfs hfi hgi).2
theorem ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, g (f x) ∂μ) ≤ g (⨍ x, f x ∂μ) :=
  (hg.average_mem_hypograph hgc hsc hfs hfi hgi).2
theorem ConvexOn.set_average_mem_epigraph (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.average_mem_epigraph hgc hsc hfs hfi hgi
theorem ConcaveOn.set_average_mem_hypograph (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa only [mem_setOf_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg
theorem ConvexOn.map_set_average_le (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
  (hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2
theorem ConcaveOn.le_map_set_average (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, g (f x) ∂μ) ≤ g (⨍ x in t, f x ∂μ) :=
  (hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2
theorem ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  simpa only [average_eq_integral] using hg.map_average_le hgc hsc hfs hfi hgi
theorem ConcaveOn.le_map_integral [IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ) := by
  simpa only [average_eq_integral] using hg.le_map_average hgc hsc hfs hfi hgi
theorem ae_eq_const_or_exists_average_ne_compl [IsFiniteMeasure μ] (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨
      ∃ t, MeasurableSet t ∧ μ t ≠ 0 ∧ μ tᶜ ≠ 0 ∧ (⨍ x in t, f x ∂μ) ≠ ⨍ x in tᶜ, f x ∂μ := by
  refine or_iff_not_imp_right.mpr fun H => ?_; push_neg at H
  refine hfi.ae_eq_of_forall_setIntegral_eq _ _ (integrable_const _) fun t ht ht' => ?_; clear ht'
  simp only [const_apply, setIntegral_const]
  by_cases h₀ : μ t = 0
  · rw [restrict_eq_zero.2 h₀, integral_zero_measure, h₀, ENNReal.zero_toReal, zero_smul]
  by_cases h₀' : μ tᶜ = 0
  · rw [← ae_eq_univ] at h₀'
    rw [restrict_congr_set h₀', restrict_univ, measure_congr h₀', measure_smul_average]
  have := average_mem_openSegment_compl_self ht.nullMeasurableSet h₀ h₀' hfi
  rw [← H t ht h₀ h₀', openSegment_same, mem_singleton_iff] at this
  rw [this, measure_smul_setAverage _ (measure_ne_top μ _)]
theorem Convex.average_mem_interior_of_set [IsFiniteMeasure μ] (hs : Convex ℝ s) (h0 : μ t ≠ 0)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (ht : (⨍ x in t, f x ∂μ) ∈ interior s) :
    (⨍ x, f x ∂μ) ∈ interior s := by
  rw [← measure_toMeasurable] at h0; rw [← restrict_toMeasurable (measure_ne_top μ t)] at ht
  by_cases h0' : μ (toMeasurable μ t)ᶜ = 0
  · rw [← ae_eq_univ] at h0'
    rwa [restrict_congr_set h0', restrict_univ] at ht
  exact
    hs.openSegment_interior_closure_subset_interior ht
      (hs.set_average_mem_closure h0' (measure_ne_top _ _) (ae_restrict_of_ae hfs)
        hfi.integrableOn)
      (average_mem_openSegment_compl_self (measurableSet_toMeasurable μ t).nullMeasurableSet h0
        h0' hfi)
theorem StrictConvex.ae_eq_const_or_average_mem_interior [IsFiniteMeasure μ] (hs : StrictConvex ℝ s)
    (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, f x ∂μ) ∈ interior s := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s := fun ht =>
    hs.convex.set_average_mem hsc ht (measure_ne_top _ _) (ae_restrict_of_ae hfs) hfi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  exact
    hs.openSegment_subset (this h₀) (this h₀') hne
      (average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' hfi)
theorem StrictConvexOn.ae_eq_const_or_map_average_lt [IsFiniteMeasure μ] (hg : StrictConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s ∧ g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
    fun ht =>
    hg.convexOn.set_average_mem_epigraph hgc hsc ht (measure_ne_top _ _) (ae_restrict_of_ae hfs)
      hfi.integrableOn hgi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  rcases average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' (hfi.prod_mk hgi) with
    ⟨a, b, ha, hb, hab, h_avg⟩
  rw [average_pair hfi hgi, average_pair hfi.integrableOn hgi.integrableOn,
    average_pair hfi.integrableOn hgi.integrableOn, Prod.smul_mk,
    Prod.smul_mk, Prod.mk_add_mk, Prod.mk.inj_iff] at h_avg
  simp only [Function.comp] at h_avg
  rw [← h_avg.1, ← h_avg.2]
  calc
    g ((a • ⨍ x in t, f x ∂μ) + b • ⨍ x in tᶜ, f x ∂μ) <
        a * g (⨍ x in t, f x ∂μ) + b * g (⨍ x in tᶜ, f x ∂μ) :=
      hg.2 (this h₀).1 (this h₀').1 hne ha hb hab
    _ ≤ (a * ⨍ x in t, g (f x) ∂μ) + b * ⨍ x in tᶜ, g (f x) ∂μ :=
      add_le_add (mul_le_mul_of_nonneg_left (this h₀).2 ha.le)
        (mul_le_mul_of_nonneg_left (this h₀').2 hb.le)
theorem StrictConcaveOn.ae_eq_const_or_lt_map_average [IsFiniteMeasure μ]
    (hg : StrictConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, g (f x) ∂μ) < g (⨍ x, f x ∂μ) := by
  simpa only [Pi.neg_apply, average_neg, neg_lt_neg_iff] using
    hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg
theorem ae_eq_const_or_norm_average_lt_of_norm_le_const [StrictConvexSpace ℝ E]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖⨍ x, f x ∂μ‖ < C := by
  rcases le_or_lt C 0 with hC0 | hC0
  · have : f =ᵐ[μ] 0 := h_le.mono fun x hx => norm_le_zero_iff.1 (hx.trans hC0)
    simp only [average_congr this, Pi.zero_apply, average_zero]
    exact Or.inl this
  by_cases hfi : Integrable f μ; swap
  · simp [average_eq, integral_undef hfi, hC0, ENNReal.toReal_pos_iff]
  rcases (le_top : μ univ ≤ ∞).eq_or_lt with hμt | hμt; · simp [average_eq, hμt, hC0]
  haveI : IsFiniteMeasure μ := ⟨hμt⟩
  replace h_le : ∀ᵐ x ∂μ, f x ∈ closedBall (0 : E) C := by simpa only [mem_closedBall_zero_iff]
  simpa only [interior_closedBall _ hC0.ne', mem_ball_zero_iff] using
    (strictConvex_closedBall ℝ (0 : E) C).ae_eq_const_or_average_mem_interior isClosed_ball h_le
      hfi
theorem ae_eq_const_or_norm_integral_lt_of_norm_le_const [StrictConvexSpace ℝ E] [IsFiniteMeasure μ]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖∫ x, f x ∂μ‖ < (μ univ).toReal * C := by
  rcases eq_or_ne μ 0 with h₀ | h₀; · left; simp [h₀, EventuallyEq]
  have hμ : 0 < (μ univ).toReal := by
    simp [ENNReal.toReal_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top]
  refine (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right fun H => ?_
  rwa [average_eq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hμ, ← div_eq_inv_mul,
    div_lt_iff₀' hμ] at H
theorem ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const [StrictConvexSpace ℝ E] (ht : μ t ≠ ∞)
    (h_le : ∀ᵐ x ∂μ.restrict t, ‖f x‖ ≤ C) :
    f =ᵐ[μ.restrict t] const α (⨍ x in t, f x ∂μ) ∨ ‖∫ x in t, f x ∂μ‖ < (μ t).toReal * C := by
  haveI := Fact.mk ht.lt_top
  rw [← restrict_apply_univ]
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le
@[deprecated (since := "2024-04-17")]
alias ae_eq_const_or_norm_set_integral_lt_of_norm_le_const :=
  ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const