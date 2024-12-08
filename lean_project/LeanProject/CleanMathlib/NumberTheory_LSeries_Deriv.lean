import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.HalfPlane
open Complex LSeries
noncomputable abbrev LSeries.logMul (f : ℕ → ℂ) (n : ℕ) : ℂ := log n * f n
lemma LSeries.hasDerivAt_term (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z ↦ term f z n) (-(term (logMul f) s n)) s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, neg_zero, hasDerivAt_const]
  simp_rw [term_of_ne_zero hn, ← neg_div, ← neg_mul, mul_comm, mul_div_assoc, div_eq_mul_inv,
    ← cpow_neg]
  exact HasDerivAt.const_mul (f n) (by simpa only [mul_comm, ← mul_neg_one (log n), ← mul_assoc]
    using (hasDerivAt_neg' s).const_cpow (Or.inl <| Nat.cast_ne_zero.mpr hn))
private lemma LSeries.LSeriesSummable_logMul_and_hasDerivAt {f : ℕ → ℂ} {s : ℂ}
    (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s ∧ HasDerivAt (LSeries f) (-LSeries (logMul f) s) s := by
  obtain ⟨x, hxs, hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  obtain ⟨y, hxy, hys⟩ := exists_between hxs
  let S : Set ℂ := {z | y < z.re}
  have h₀ : Summable (fun n ↦ ‖term f x n‖) := summable_norm_iff.mpr hf
  have h₁ (n) : DifferentiableOn ℂ (term f · n) S :=
    fun z _ ↦ (hasDerivAt_term f n _).differentiableAt.differentiableWithinAt
  have h₂ : IsOpen S := isOpen_lt continuous_const continuous_re
  have h₃ (n z) (hz : z ∈ S) : ‖term f z n‖ ≤ ‖term f x n‖ :=
    norm_term_le_of_re_le_re f (by simpa using (hxy.trans hz).le) n
  have H := hasSum_deriv_of_summable_norm h₀ h₁ h₂ h₃ hys
  simp_rw [(hasDerivAt_term f _ _).deriv] at H
  refine ⟨summable_neg_iff.mp H.summable, ?_⟩
  have H' := differentiableOn_tsum_of_summable_norm h₀ h₁ h₂ h₃
  simpa only [← H.tsum_eq, tsum_neg]
    using (H'.differentiableAt <| IsOpen.mem_nhds h₂ hys).hasDerivAt
lemma LSeries_hasDerivAt {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    HasDerivAt (LSeries f) (- LSeries (logMul f) s) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).2
lemma LSeries_deriv {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    deriv (LSeries f) s = - LSeries (logMul f) s :=
  (LSeries_hasDerivAt h).deriv
lemma LSeries_deriv_eqOn {f : ℕ → ℂ} :
    {s | abscissaOfAbsConv f < s.re}.EqOn (deriv (LSeries f)) (- LSeries (logMul f)) :=
  deriv_eqOn (isOpen_re_gt_EReal _) fun _ hs ↦ (LSeries_hasDerivAt hs).hasDerivWithinAt
lemma LSeriesSummable_logMul_of_lt_re {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).1
@[simp]
lemma LSeries.abscissaOfAbsConv_logMul {f : ℕ → ℂ} :
    abscissaOfAbsConv (logMul f) = abscissaOfAbsConv f := by
  apply le_antisymm <;> refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun s hs ↦ ?_
  · exact LSeriesSummable_logMul_of_lt_re <| by simp [hs]
  · refine (LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simp only [ofReal_re, hs])
      |>.norm.of_norm_bounded_eventually_nat (‖term (logMul f) s ·‖) ?_
    filter_upwards [Filter.eventually_ge_atTop <| max 1 (Nat.ceil (Real.exp 1))] with n hn
    simp only [term_of_ne_zero (show n ≠ 0 by omega), logMul, norm_mul, mul_div_assoc,
      ← natCast_log, norm_real]
    refine le_mul_of_one_le_left (norm_nonneg _) (.trans ?_ <| Real.le_norm_self _)
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) <| Nat.ceil_le.mp <| (le_max_right _ _).trans hn
@[simp]
lemma LSeries.absicssaOfAbsConv_logPowMul {f : ℕ → ℂ} {m : ℕ} :
    abscissaOfAbsConv (logMul^[m] f) = abscissaOfAbsConv f := by
  induction' m with n ih
  · simp only [Function.iterate_zero, id_eq]
  · simp only [ih, Function.iterate_succ', Function.comp_def, abscissaOfAbsConv_logMul]
lemma LSeries_iteratedDeriv {f : ℕ → ℂ} (m : ℕ) {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    iteratedDeriv m (LSeries f) s = (-1) ^ m * LSeries (logMul^[m] f) s := by
  induction' m with m ih generalizing s
  · simp only [iteratedDeriv_zero, pow_zero, Function.iterate_zero, id_eq, one_mul]
  · have ih' : {s | abscissaOfAbsConv f < re s}.EqOn (iteratedDeriv m (LSeries f))
        ((-1) ^ m * LSeries (logMul^[m] f)) := fun _ hs ↦ ih hs
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOpen_re_gt_EReal _) h] at this
    rw [iteratedDeriv_succ, this]
    simp only [Pi.mul_def, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, deriv_const_mul_field',
      pow_succ, mul_assoc, neg_one_mul, Function.iterate_succ', Function.comp_def,
      LSeries_deriv <| absicssaOfAbsConv_logPowMul.symm ▸ h]
lemma LSeries_differentiableOn (f : ℕ → ℂ) :
    DifferentiableOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  fun _ hz ↦ (LSeries_hasDerivAt hz).differentiableAt.differentiableWithinAt
lemma LSeries_analyticOnNhd (f : ℕ → ℂ) :
    AnalyticOnNhd ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries_differentiableOn f).analyticOnNhd <| isOpen_re_gt_EReal _
lemma LSeries_analyticOn (f : ℕ → ℂ) :
    AnalyticOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries_analyticOnNhd f).analyticOn