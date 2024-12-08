import Mathlib.Analysis.BoxIntegral.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Tactic.Generalize
open scoped NNReal ENNReal Topology
universe u v
variable {ι : Type u} {E : Type v} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
open MeasureTheory Metric Set Finset Filter BoxIntegral
namespace BoxIntegral
theorem hasIntegralIndicatorConst (l : IntegrationParams) (hl : l.bRiemann = false)
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (I : Box ι) (y : E) (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] :
    HasIntegral.{u, v, v} I l (s.indicator fun _ => y) μ.toBoxAdditive.toSMul
      ((μ (s ∩ I)).toReal • y) := by
  refine HasIntegral.of_mul ‖y‖ fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le; rw [NNReal.coe_pos] at ε0
  have A : μ (s ∩ Box.Icc I) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt (I.measure_Icc_lt_top μ)).ne
  have B : μ (s ∩ I) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt (I.measure_coe_lt_top μ)).ne
  obtain ⟨F, hFs, hFc, hμF⟩ : ∃ F, F ⊆ s ∩ Box.Icc I ∧ IsClosed F ∧ μ ((s ∩ Box.Icc I) \ F) < ε :=
    (hs.inter I.measurableSet_Icc).exists_isClosed_diff_lt A (ENNReal.coe_pos.2 ε0).ne'
  obtain ⟨U, hsU, hUo, hUt, hμU⟩ :
      ∃ U, s ∩ Box.Icc I ⊆ U ∧ IsOpen U ∧ μ U < ∞ ∧ μ (U \ (s ∩ Box.Icc I)) < ε :=
    (hs.inter I.measurableSet_Icc).exists_isOpen_diff_lt A (ENNReal.coe_pos.2 ε0).ne'
  have : ∀ x ∈ s ∩ Box.Icc I, ∃ r : Ioi (0 : ℝ), closedBall x r ⊆ U := fun x hx => by
    rcases nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds <| hsU hx) with ⟨r, hr₀, hr⟩
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose! rs hrsU using this
  have : ∀ x ∈ Box.Icc I \ s, ∃ r : Ioi (0 : ℝ), closedBall x r ⊆ Fᶜ := fun x hx => by
    obtain ⟨r, hr₀, hr⟩ :=
      nhds_basis_closedBall.mem_iff.1 (hFc.isOpen_compl.mem_nhds fun hx' => hx.2 (hFs hx').1)
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose! rs' hrs'F using this
  classical
  set r : (ι → ℝ) → Ioi (0 : ℝ) := s.piecewise rs rs'
  refine ⟨fun _ => r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ hπp => ?_⟩; rw [mul_comm]
  dsimp [integralSum]
  simp only [mem_closedBall, dist_eq_norm, ← indicator_const_smul_apply,
    sum_indicator_eq_sum_filter, ← sum_smul, ← sub_smul, norm_smul, Real.norm_eq_abs, ←
    Prepartition.filter_boxes, ← Prepartition.measure_iUnion_toReal]
  gcongr
  set t := (π.filter (π.tag · ∈ s)).iUnion
  change abs ((μ t).toReal - (μ (s ∩ I)).toReal) ≤ ε
  have htU : t ⊆ U ∩ I := by
    simp only [t, TaggedPrepartition.iUnion_def, iUnion_subset_iff, TaggedPrepartition.mem_filter,
      and_imp]
    refine fun J hJ hJs x hx => ⟨hrsU _ ⟨hJs, π.tag_mem_Icc J⟩ ?_, π.le_of_mem' J hJ hx⟩
    simpa only [r, s.piecewise_eq_of_mem _ _ hJs] using hπ.1 J hJ (Box.coe_subset_Icc hx)
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · refine (ENNReal.le_toReal_sub B).trans (ENNReal.toReal_le_coe_of_le_coe ?_)
    refine (tsub_le_tsub (measure_mono htU) le_rfl).trans (le_measure_diff.trans ?_)
    refine (measure_mono fun x hx => ?_).trans hμU.le
    exact ⟨hx.1.1, fun hx' => hx.2 ⟨hx'.1, hx.1.2⟩⟩
  · have hμt : μ t ≠ ∞ := ((measure_mono (htU.trans inter_subset_left)).trans_lt hUt).ne
    refine (ENNReal.le_toReal_sub hμt).trans (ENNReal.toReal_le_coe_of_le_coe ?_)
    refine le_measure_diff.trans ((measure_mono ?_).trans hμF.le)
    rintro x ⟨⟨hxs, hxI⟩, hxt⟩
    refine ⟨⟨hxs, Box.coe_subset_Icc hxI⟩, fun hxF => hxt ?_⟩
    simp only [t, TaggedPrepartition.iUnion_def, TaggedPrepartition.mem_filter, Set.mem_iUnion]
    rcases hπp x hxI with ⟨J, hJπ, hxJ⟩
    refine ⟨J, ⟨hJπ, ?_⟩, hxJ⟩
    contrapose hxF
    refine hrs'F _ ⟨π.tag_mem_Icc J, hxF⟩ ?_
    simpa only [r, s.piecewise_eq_of_not_mem _ _ hxF] using hπ.1 J hJπ (Box.coe_subset_Icc hxJ)
theorem HasIntegral.of_aeEq_zero {l : IntegrationParams} {I : Box ι} {f : (ι → ℝ) → E}
    {μ : Measure (ι → ℝ)} [IsLocallyFiniteMeasure μ] (hf : f =ᵐ[μ.restrict I] 0)
    (hl : l.bRiemann = false) : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul 0 := by
  refine hasIntegral_iff.2 fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.lt.le; rw [gt_iff_lt, NNReal.coe_pos] at ε0
  rcases NNReal.exists_pos_sum_of_countable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩
  haveI := Fact.mk (I.measure_coe_lt_top μ)
  change μ.restrict I {x | f x ≠ 0} = 0 at hf
  set N : (ι → ℝ) → ℕ := fun x => ⌈‖f x‖⌉₊
  have N0 : ∀ {x}, N x = 0 ↔ f x = 0 := by simp [N]
  have : ∀ n, ∃ U, N ⁻¹' {n} ⊆ U ∧ IsOpen U ∧ μ.restrict I U < δ n / n := fun n ↦ by
    refine (N ⁻¹' {n}).exists_isOpen_lt_of_lt _ ?_
    cases' n with n
    · simp [ENNReal.div_zero (ENNReal.coe_pos.2 (δ0 _)).ne']
    · refine (measure_mono_null ?_ hf).le.trans_lt ?_
      · exact fun x hxN hxf => n.succ_ne_zero ((Eq.symm hxN).trans <| N0.2 hxf)
      · simp [(δ0 _).ne']
  choose U hNU hUo hμU using this
  have : ∀ x, ∃ r : Ioi (0 : ℝ), closedBall x r ⊆ U (N x) := fun x => by
    obtain ⟨r, hr₀, hr⟩ := nhds_basis_closedBall.mem_iff.1 ((hUo _).mem_nhds (hNU _ rfl))
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose r hrU using this
  refine ⟨fun _ => r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ _ => ?_⟩
  rw [dist_eq_norm, sub_zero, ← integralSum_fiberwise fun J => N (π.tag J)]
  refine le_trans ?_ (NNReal.coe_lt_coe.2 hcε).le
  refine (norm_sum_le_of_le _ ?_).trans
    (sum_le_hasSum _ (fun n _ => (δ n).2) (NNReal.hasSum_coe.2 hδc))
  rintro n -
  dsimp [integralSum]
  have : ∀ J ∈ π.filter fun J => N (π.tag J) = n,
      ‖(μ ↑J).toReal • f (π.tag J)‖ ≤ (μ J).toReal * n := fun J hJ ↦ by
    rw [TaggedPrepartition.mem_filter] at hJ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    gcongr
    exact hJ.2 ▸ Nat.le_ceil _
  refine (norm_sum_le_of_le _ this).trans ?_; clear this
  rw [← sum_mul, ← Prepartition.measure_iUnion_toReal]
  let m := μ (π.filter fun J => N (π.tag J) = n).iUnion
  show m.toReal * ↑n ≤ ↑(δ n)
  have : m < δ n / n := by
    simp only [Measure.restrict_apply (hUo _).measurableSet] at hμU
    refine (measure_mono ?_).trans_lt (hμU _)
    simp only [Set.subset_def, TaggedPrepartition.mem_iUnion, TaggedPrepartition.mem_filter]
    rintro x ⟨J, ⟨hJ, rfl⟩, hx⟩
    exact ⟨hrU _ (hπ.1 _ hJ (Box.coe_subset_Icc hx)), π.le_of_mem' J hJ hx⟩
  clear_value m
  lift m to ℝ≥0 using ne_top_of_lt this
  rw [ENNReal.coe_toReal, ← NNReal.coe_natCast, ← NNReal.coe_mul, NNReal.coe_le_coe, ←
    ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_natCast, mul_comm]
  exact (mul_le_mul_left' this.le _).trans ENNReal.mul_div_le
theorem HasIntegral.congr_ae {l : IntegrationParams} {I : Box ι} {y : E} {f g : (ι → ℝ) → E}
    {μ : Measure (ι → ℝ)} [IsLocallyFiniteMeasure μ]
    (hf : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul y) (hfg : f =ᵐ[μ.restrict I] g)
    (hl : l.bRiemann = false) : HasIntegral.{u, v, v} I l g μ.toBoxAdditive.toSMul y := by
  have : g - f =ᵐ[μ.restrict I] 0 := hfg.mono fun x hx => sub_eq_zero.2 hx.symm
  simpa using hf.add (HasIntegral.of_aeEq_zero this hl)
end BoxIntegral
namespace MeasureTheory
namespace SimpleFunc
theorem hasBoxIntegral (f : SimpleFunc (ι → ℝ) E) (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : Box ι) (l : IntegrationParams) (hl : l.bRiemann = false) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (f.integral (μ.restrict I)) := by
  induction' f using MeasureTheory.SimpleFunc.induction with y s hs f g _ hfi hgi
  · simpa only [Measure.restrict_apply hs, const_zero, integral_piecewise_zero, integral_const,
      Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter] using
      BoxIntegral.hasIntegralIndicatorConst l hl hs I y μ
  · borelize E; haveI := Fact.mk (I.measure_coe_lt_top μ)
    rw [integral_add]
    exacts [hfi.add hgi, integrable_iff.2 fun _ _ => measure_lt_top _ _,
      integrable_iff.2 fun _ _ => measure_lt_top _ _]
theorem box_integral_eq_integral (f : SimpleFunc (ι → ℝ) E) (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] (I : Box ι) (l : IntegrationParams) (hl : l.bRiemann = false) :
    BoxIntegral.integral.{u, v, v} I l f μ.toBoxAdditive.toSMul = f.integral (μ.restrict I) :=
  (f.hasBoxIntegral μ I l hl).integral_eq
end SimpleFunc
open TopologicalSpace
theorem IntegrableOn.hasBoxIntegral [CompleteSpace E] {f : (ι → ℝ) → E} {μ : Measure (ι → ℝ)}
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hf : IntegrableOn f I μ) (l : IntegrationParams)
    (hl : l.bRiemann = false) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  borelize E
  rcases hf.aestronglyMeasurable with ⟨g, hg, hfg⟩
  haveI : SeparableSpace (range g ∪ {0} : Set E) := hg.separableSpace_range_union_singleton
  rw [integral_congr_ae hfg]; have hgi : IntegrableOn g I μ := (integrable_congr hfg).1 hf
  refine BoxIntegral.HasIntegral.congr_ae ?_ hfg.symm hl
  clear! f
  set f : ℕ → SimpleFunc (ι → ℝ) E :=
    SimpleFunc.approxOn g hg.measurable (range g ∪ {0}) 0 (by simp)
  have hfi : ∀ n, IntegrableOn (f n) I μ :=
    SimpleFunc.integrable_approxOn_range hg.measurable hgi
  have hfi' := fun n => ((f n).hasBoxIntegral μ I l hl).integrable
  have hfg_mono : ∀ (x) {m n}, m ≤ n → ‖f n x - g x‖ ≤ ‖f m x - g x‖ := by
    intro x m n hmn
    rw [← dist_eq_norm, ← dist_eq_norm, dist_nndist, dist_nndist, NNReal.coe_le_coe, ←
      ENNReal.coe_le_coe, ← edist_nndist, ← edist_nndist]
    exact SimpleFunc.edist_approxOn_mono hg.measurable _ x hmn
  refine HasIntegral.of_mul ((μ I).toReal + 1 + 1) fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le; rw [NNReal.coe_pos] at ε0; have ε0' := ENNReal.coe_pos.2 ε0
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, ∫ x in I, ‖f N x - g x‖ ∂μ ≤ ε := by
    have : Tendsto (fun n => ∫⁻ x in I, ‖f n x - g x‖₊ ∂μ) atTop (𝓝 0) :=
      SimpleFunc.tendsto_approxOn_range_L1_nnnorm hg.measurable hgi
    refine (this.eventually (ge_mem_nhds ε0')).exists.imp fun N hN => ?_
    exact integral_coe_le_of_lintegral_coe_le hN
  have : ∀ x, ∃ N₁, N₀ ≤ N₁ ∧ dist (f N₁ x) (g x) ≤ ε := fun x ↦ by
    have : Tendsto (f · x) atTop (𝓝 <| g x) :=
      SimpleFunc.tendsto_approxOn hg.measurable _ (subset_closure (by simp))
    exact ((eventually_ge_atTop N₀).and <| this <| closedBall_mem_nhds _ ε0).exists
  choose Nx hNx hNxε using this
  rcases NNReal.exists_pos_sum_of_countable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩
  set r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) := fun c x => (hfi' <| Nx x).convergenceR (δ <| Nx x) c x
  refine ⟨r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ hπp => ?_⟩
  refine (dist_triangle4 _ (∑ J ∈ π.boxes, (μ J).toReal • f (Nx <| π.tag J) (π.tag J))
    (∑ J ∈ π.boxes, ∫ x in J, f (Nx <| π.tag J) x ∂μ) _).trans ?_
  rw [add_mul, add_mul, one_mul]
  refine add_le_add_three ?_ ?_ ?_
  · 
    rw [← hπp.iUnion_eq, π.measure_iUnion_toReal, sum_mul, integralSum]
    refine dist_sum_sum_le_of_le _ fun J _ => ?_; dsimp
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    gcongr
    rw [← dist_eq_norm']; exact hNxε _
  · 
    rw [← π.sum_fiberwise fun J => Nx (π.tag J), ← π.sum_fiberwise fun J => Nx (π.tag J)]
    refine le_trans ?_ (NNReal.coe_lt_coe.2 hcε).le
    refine
      (dist_sum_sum_le_of_le _ fun n hn => ?_).trans
        (sum_le_hasSum _ (fun n _ => (δ n).2) (NNReal.hasSum_coe.2 hδc))
    have hNxn : ∀ J ∈ π.filter fun J => Nx (π.tag J) = n, Nx (π.tag J) = n := fun J hJ =>
      (π.mem_filter.1 hJ).2
    have hrn : ∀ J ∈ π.filter fun J => Nx (π.tag J) = n,
        r c (π.tag J) = (hfi' n).convergenceR (δ n) c (π.tag J) := fun J hJ ↦ by
      obtain rfl := hNxn J hJ
      rfl
    have :
        l.MemBaseSet I c ((hfi' n).convergenceR (δ n) c) (π.filter fun J => Nx (π.tag J) = n) :=
      (hπ.filter _).mono' _ le_rfl le_rfl fun J hJ => (hrn J hJ).le
    convert (hfi' n).dist_integralSum_sum_integral_le_of_memBaseSet (δ0 _) this using 2
    · refine sum_congr rfl fun J hJ => ?_
      simp [hNxn J hJ]
    · refine sum_congr rfl fun J hJ => ?_
      rw [← SimpleFunc.integral_eq_integral, SimpleFunc.box_integral_eq_integral _ _ _ _ hl,
        hNxn J hJ]
      exact (hfi _).mono_set (Prepartition.le_of_mem _ hJ)
  · 
    refine le_trans ?_ hN₀
    have hfi : ∀ (n), ∀ J ∈ π, IntegrableOn (f n) (↑J) μ := fun n J hJ =>
      (hfi n).mono_set (π.le_of_mem' J hJ)
    have hgi : ∀ J ∈ π, IntegrableOn g (↑J) μ := fun J hJ => hgi.mono_set (π.le_of_mem' J hJ)
    have hfgi : ∀ (n), ∀ J ∈ π, IntegrableOn (fun x => ‖f n x - g x‖) J μ := fun n J hJ =>
      ((hfi n J hJ).sub (hgi J hJ)).norm
    rw [← hπp.iUnion_eq, Prepartition.iUnion_def',
      integral_finset_biUnion π.boxes (fun J _ => J.measurableSet_coe) π.pairwiseDisjoint hgi,
      integral_finset_biUnion π.boxes (fun J _ => J.measurableSet_coe) π.pairwiseDisjoint (hfgi _)]
    refine dist_sum_sum_le_of_le _ fun J hJ => ?_
    rw [dist_eq_norm, ← integral_sub (hfi _ J hJ) (hgi J hJ)]
    refine norm_integral_le_of_norm_le (hfgi _ J hJ) (Eventually.of_forall fun x => ?_)
    exact hfg_mono x (hNx (π.tag J))
theorem ContinuousOn.hasBoxIntegral [CompleteSpace E] {f : (ι → ℝ) → E} (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hc : ContinuousOn f (Box.Icc I))
    (l : IntegrationParams) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  obtain ⟨y, hy⟩ := BoxIntegral.integrable_of_continuousOn l hc μ
  convert hy
  have : IntegrableOn f I μ :=
    IntegrableOn.mono_set (hc.integrableOn_compact I.isCompact_Icc) Box.coe_subset_Icc
  exact HasIntegral.unique (IntegrableOn.hasBoxIntegral this ⊥ rfl) (HasIntegral.mono hy bot_le)
theorem AEContinuous.hasBoxIntegral [CompleteSpace E] {f : (ι → ℝ) → E} (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hb : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖f x‖ ≤ C)
    (hc : ∀ᵐ x ∂μ, ContinuousAt f x) (l : IntegrationParams) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  obtain ⟨y, hy⟩ := integrable_of_bounded_and_ae_continuous l hb μ hc
  convert hy
  refine HasIntegral.unique (IntegrableOn.hasBoxIntegral ?_ ⊥ rfl) (HasIntegral.mono hy bot_le)
  constructor
  · let v := {x : (ι → ℝ) | ContinuousAt f x}
    have : AEStronglyMeasurable f (μ.restrict v) :=
      (continuousOn_of_forall_continuousAt fun _ h ↦ h).aestronglyMeasurable
      (measurableSet_of_continuousAt f)
    refine this.mono_measure (Measure.le_iff.2 fun s hs ↦ ?_)
    repeat rw [μ.restrict_apply hs]
    apply le_of_le_of_eq <| μ.mono s.inter_subset_left
    refine measure_eq_measure_of_null_diff s.inter_subset_left ?_ |>.symm
    rw [diff_self_inter, Set.diff_eq]
    refine (le_antisymm (zero_le (μ (s ∩ vᶜ))) ?_).symm
    exact le_trans (μ.mono s.inter_subset_right) (nonpos_iff_eq_zero.2 hc)
  · have : IsFiniteMeasure (μ.restrict (Box.Icc I)) :=
      { measure_univ_lt_top := by simp [I.isCompact_Icc.measure_lt_top (μ := μ)] }
    have : IsFiniteMeasure (μ.restrict I) :=
      isFiniteMeasure_of_le (μ.restrict (Box.Icc I))
                            (μ.restrict_mono Box.coe_subset_Icc (le_refl μ))
    obtain ⟨C, hC⟩ := hb
    refine hasFiniteIntegral_of_bounded (C := C) (Filter.eventually_iff_exists_mem.2 ?_)
    use I, self_mem_ae_restrict I.measurableSet_coe, fun y hy ↦ hC y (I.coe_subset_Icc hy)
end MeasureTheory