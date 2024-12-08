import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.Order.Monotone.Extension
open Set Filter Function Metric MeasureTheory MeasureTheory.Measure IsUnifLocDoublingMeasure
open scoped Topology
theorem tendsto_apply_add_mul_sq_div_sub {f : ℝ → ℝ} {x a c d : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝[≠] x)
    (hf : Tendsto (fun y => (f y - d) / (y - x)) l (𝓝 a))
    (h' : Tendsto (fun y => y + c * (y - x) ^ 2) l l) :
    Tendsto (fun y => (f (y + c * (y - x) ^ 2) - d) / (y - x)) l (𝓝 a) := by
  have L : Tendsto (fun y => (y + c * (y - x) ^ 2 - x) / (y - x)) l (𝓝 1) := by
    have : Tendsto (fun y => 1 + c * (y - x)) l (𝓝 (1 + c * (x - x))) := by
      apply Tendsto.mono_left _ (hl.trans nhdsWithin_le_nhds)
      exact ((tendsto_id.sub_const x).const_mul c).const_add 1
    simp only [_root_.sub_self, add_zero, mul_zero] at this
    apply Tendsto.congr' (Eventually.filter_mono hl _) this
    filter_upwards [self_mem_nhdsWithin] with y hy
    field_simp [sub_ne_zero.2 hy]
    ring
  have Z := (hf.comp h').mul L
  rw [mul_one] at Z
  apply Tendsto.congr' _ Z
  have : ∀ᶠ y in l, y + c * (y - x) ^ 2 ≠ x := by apply Tendsto.mono_right h' hl self_mem_nhdsWithin
  filter_upwards [this] with y hy
  field_simp [sub_ne_zero.2 hy]
theorem StieltjesFunction.ae_hasDerivAt (f : StieltjesFunction) :
    ∀ᵐ x, HasDerivAt f (rnDeriv f.measure volume x).toReal x := by
  filter_upwards [VitaliFamily.ae_tendsto_rnDeriv (vitaliFamily (volume : Measure ℝ) 1) f.measure,
    rnDeriv_lt_top f.measure volume, f.countable_leftLim_ne.ae_not_mem volume] with x hx h'x h''x
  have L1 :
    Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[>] x) (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply Tendsto.congr' _
      ((ENNReal.tendsto_toReal h'x.ne).comp (hx.comp (Real.tendsto_Icc_vitaliFamily_right x)))
    filter_upwards [self_mem_nhdsWithin]
    rintro y (hxy : x < y)
    simp only [comp_apply, StieltjesFunction.measure_Icc, Real.volume_Icc, Classical.not_not.1 h''x]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal]
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le
  have L2 : Tendsto (fun y => (leftLim f y - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply Tendsto.congr' _
      ((ENNReal.tendsto_toReal h'x.ne).comp (hx.comp (Real.tendsto_Icc_vitaliFamily_left x)))
    filter_upwards [self_mem_nhdsWithin]
    rintro y (hxy : y < x)
    simp only [comp_apply, StieltjesFunction.measure_Icc, Real.volume_Icc]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal, ← neg_neg (y - x),
      div_neg, neg_div', neg_sub, neg_sub]
    exact div_nonneg (sub_nonneg.2 (f.mono.leftLim_le hxy.le)) (sub_pos.2 hxy).le
  have L3 : Tendsto (fun y => (leftLim f (y + 1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply tendsto_apply_add_mul_sq_div_sub (nhds_left'_le_nhds_ne x) L2
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have : Tendsto (fun y : ℝ => y + ↑1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + ↑1 * (x - x) ^ 2)) :=
        tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul ↑1)
      simpa using this
    · have : Ioo (x - 1) x ∈ 𝓝[<] x := by
        apply Ioo_mem_nhdsWithin_Iio; exact ⟨by linarith, le_refl _⟩
      filter_upwards [this]
      rintro y ⟨hy : x - 1 < y, h'y : y < x⟩
      rw [mem_Iio]
      nlinarith
  have L4 :
    Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[<] x) (𝓝 (rnDeriv f.measure volume x).toReal) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' L3 L2
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      refine div_le_div_of_nonpos_of_le (by linarith) ((sub_le_sub_iff_right _).2 ?_)
      apply f.mono.le_leftLim
      have : ↑0 < (x - y) ^ 2 := sq_pos_of_pos (sub_pos.2 hy)
      linarith
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      refine div_le_div_of_nonpos_of_le (by linarith) ?_
      simpa only [sub_le_sub_iff_right] using f.mono.leftLim_le (le_refl y)
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, ← nhds_left'_sup_nhds_right', tendsto_sup]
  exact ⟨L4, L1⟩
theorem Monotone.ae_hasDerivAt {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x, HasDerivAt f (rnDeriv hf.stieltjesFunction.measure volume x).toReal x := by
  filter_upwards [hf.stieltjesFunction.ae_hasDerivAt,
    hf.countable_not_continuousAt.ae_not_mem volume] with x hx h'x
  have A : hf.stieltjesFunction x = f x := by
    rw [Classical.not_not, hf.continuousAt_iff_leftLim_eq_rightLim] at h'x
    apply le_antisymm _ (hf.le_rightLim (le_refl _))
    rw [← h'x]
    exact hf.leftLim_le (le_refl _)
  rw [hasDerivAt_iff_tendsto_slope, (nhds_left'_sup_nhds_right' x).symm, tendsto_sup,
    slope_fun_def_field, A] at hx
  have L1 : Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[>] x)
      (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
    have : Tendsto (fun y => (hf.stieltjesFunction (y + -1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[>] x)
        (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
      apply tendsto_apply_add_mul_sq_div_sub (nhds_right'_le_nhds_ne x) hx.2
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have : Tendsto (fun y : ℝ => y + -↑1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + -↑1 * (x - x) ^ 2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1))
        simpa using this
      · have : Ioo x (x + 1) ∈ 𝓝[>] x := by
          apply Ioo_mem_nhdsWithin_Ioi; exact ⟨le_refl _, by linarith⟩
        filter_upwards [this]
        rintro y ⟨hy : x < y, h'y : y < x + 1⟩
        rw [mem_Ioi]
        nlinarith
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' this hx.2
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [mem_Ioi, ← sub_pos] at hy
      gcongr
      exact hf.rightLim_le (by nlinarith)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [mem_Ioi, ← sub_pos] at hy
      gcongr
      exact hf.le_rightLim le_rfl
  have L2 : Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
    have : Tendsto (fun y => (hf.stieltjesFunction (y + -1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[<] x)
        (𝓝 (rnDeriv hf.stieltjesFunction.measure volume x).toReal) := by
      apply tendsto_apply_add_mul_sq_div_sub (nhds_left'_le_nhds_ne x) hx.1
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have : Tendsto (fun y : ℝ => y + -↑1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + -↑1 * (x - x) ^ 2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1))
        simpa using this
      · have : Ioo (x - 1) x ∈ 𝓝[<] x := by
          apply Ioo_mem_nhdsWithin_Iio; exact ⟨by linarith, le_refl _⟩
        filter_upwards [this]
        rintro y hy
        rw [mem_Ioo] at hy
        rw [mem_Iio]
        nlinarith
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hx.1 this
    · filter_upwards [self_mem_nhdsWithin]
      rintro y hy
      rw [mem_Iio, ← sub_neg] at hy
      apply div_le_div_of_nonpos_of_le hy.le
      exact (sub_le_sub_iff_right _).2 (hf.le_rightLim (le_refl _))
    · filter_upwards [self_mem_nhdsWithin]
      rintro y hy
      rw [mem_Iio, ← sub_neg] at hy
      have : 0 < (y - x) ^ 2 := sq_pos_of_neg hy
      apply div_le_div_of_nonpos_of_le hy.le
      exact (sub_le_sub_iff_right _).2 (hf.rightLim_le (by linarith))
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, (nhds_left'_sup_nhds_right' x).symm,
    tendsto_sup]
  exact ⟨L2, L1⟩
theorem Monotone.ae_differentiableAt {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_hasDerivAt] with x hx using hx.differentiableAt
theorem MonotoneOn.ae_differentiableWithinAt_of_mem {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s) :
    ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  apply ae_of_mem_of_ae_of_mem_inter_Ioo
  intro a b as bs _
  obtain ⟨g, hg, gf⟩ : ∃ g : ℝ → ℝ, Monotone g ∧ EqOn f g (s ∩ Icc a b) :=
    (hf.mono inter_subset_left).exists_monotone_extension
      (hf.map_bddBelow inter_subset_left ⟨a, fun x hx => hx.2.1, as⟩)
      (hf.map_bddAbove inter_subset_left ⟨b, fun x hx => hx.2.2, bs⟩)
  filter_upwards [hg.ae_differentiableAt] with x hx
  intro h'x
  apply hx.differentiableWithinAt.congr_of_eventuallyEq _ (gf ⟨h'x.1, h'x.2.1.le, h'x.2.2.le⟩)
  have : Ioo a b ∈ 𝓝[s] x := nhdsWithin_le_nhds (Ioo_mem_nhds h'x.2.1 h'x.2.2)
  filter_upwards [self_mem_nhdsWithin, this] with y hy h'y
  exact gf ⟨hy, h'y.1.le, h'y.2.le⟩
theorem MonotoneOn.ae_differentiableWithinAt {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem