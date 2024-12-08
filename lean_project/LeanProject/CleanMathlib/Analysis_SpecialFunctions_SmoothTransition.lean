import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
noncomputable section
open scoped Topology
open Polynomial Real Filter Set Function
def expNegInvGlue (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-x⁻¹)
namespace expNegInvGlue
theorem zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : expNegInvGlue x = 0 := by simp [expNegInvGlue, hx]
@[simp]
protected theorem zero : expNegInvGlue 0 = 0 := zero_of_nonpos le_rfl
theorem pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < expNegInvGlue x := by
  simp [expNegInvGlue, not_le.2 hx, exp_pos]
theorem nonneg (x : ℝ) : 0 ≤ expNegInvGlue x := by
  cases le_or_gt x 0 with
  | inl h => exact ge_of_eq (zero_of_nonpos h)
  | inr h => exact le_of_lt (pos_of_pos h)
@[simp] theorem zero_iff_nonpos {x : ℝ} : expNegInvGlue x = 0 ↔ x ≤ 0 :=
  ⟨fun h ↦ not_lt.mp fun h' ↦ (pos_of_pos h').ne' h, zero_of_nonpos⟩
theorem tendsto_polynomial_inv_mul_zero (p : ℝ[X]) :
    Tendsto (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) (𝓝 0) (𝓝 0) := by
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have : Tendsto (fun x ↦ p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) :=
    p.tendsto_div_exp_atTop.comp tendsto_inv_zero_atTop
  refine this.congr' <| mem_of_superset self_mem_nhdsWithin fun x hx ↦ ?_
  simp [expNegInvGlue, hx.out.not_le, exp_neg, div_eq_mul_inv]
theorem hasDerivAt_polynomial_eval_inv_mul (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * expNegInvGlue x)
      ((X ^ 2 * (p - derivative (R := ℝ) p)).eval x⁻¹ * expNegInvGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [zero_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [zero_of_nonpos hy.le, mul_zero]
  · rw [expNegInvGlue.zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_zero (p * X)).mono_left inf_le_left).congr fun x ↦ ?_
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have := ((p.hasDerivAt x⁻¹).mul (hasDerivAt_neg _).exp).comp x (hasDerivAt_inv hx.ne')
    convert this.congr_of_eventuallyEq _ using 1
    · simp [expNegInvGlue, hx.not_le]
      ring
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp [expNegInvGlue, hy.not_le]
theorem differentiable_polynomial_eval_inv_mul (p : ℝ[X]) :
    Differentiable ℝ (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) := fun x ↦
  (hasDerivAt_polynomial_eval_inv_mul p x).differentiableAt
theorem continuous_polynomial_eval_inv_mul (p : ℝ[X]) :
    Continuous (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) :=
  (differentiable_polynomial_eval_inv_mul p).continuous
theorem contDiff_polynomial_eval_inv_mul {n : ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing p with
  | zero => exact contDiff_zero.2 <| continuous_polynomial_eval_inv_mul _
  | succ m ihm =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_polynomial_eval_inv_mul _, by simp, ?_⟩
    convert ihm (X ^ 2 * (p - derivative (R := ℝ) p)) using 2
    exact (hasDerivAt_polynomial_eval_inv_mul p _).deriv
protected theorem contDiff {n : ℕ∞} : ContDiff ℝ n expNegInvGlue := by
  simpa using contDiff_polynomial_eval_inv_mul 1
end expNegInvGlue
def Real.smoothTransition (x : ℝ) : ℝ :=
  expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))
namespace Real
namespace smoothTransition
variable {x : ℝ}
open expNegInvGlue
theorem pos_denom (x) : 0 < expNegInvGlue x + expNegInvGlue (1 - x) :=
  (zero_lt_one.lt_or_lt x).elim (fun hx => add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
    fun hx => add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos <| sub_pos.2 hx)
theorem one_of_one_le (h : 1 ≤ x) : smoothTransition x = 1 :=
  (div_eq_one_iff_eq <| (pos_denom x).ne').2 <| by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]
@[simp]
nonrec theorem zero_iff_nonpos : smoothTransition x = 0 ↔ x ≤ 0 := by
  simp only [smoothTransition, _root_.div_eq_zero_iff, (pos_denom x).ne', zero_iff_nonpos, or_false]
theorem zero_of_nonpos (h : x ≤ 0) : smoothTransition x = 0 := zero_iff_nonpos.2 h
@[simp]
protected theorem zero : smoothTransition 0 = 0 :=
  zero_of_nonpos le_rfl
@[simp]
protected theorem one : smoothTransition 1 = 1 :=
  one_of_one_le le_rfl
@[simp]
protected theorem projIcc :
    smoothTransition (projIcc (0 : ℝ) 1 zero_le_one x) = smoothTransition x := by
  refine congr_fun
    (IccExtend_eq_self zero_le_one smoothTransition (fun x hx => ?_) fun x hx => ?_) x
  · rw [smoothTransition.zero, zero_of_nonpos hx.le]
  · rw [smoothTransition.one, one_of_one_le hx.le]
theorem le_one (x : ℝ) : smoothTransition x ≤ 1 :=
  (div_le_one (pos_denom x)).2 <| le_add_of_nonneg_right (nonneg _)
theorem nonneg (x : ℝ) : 0 ≤ smoothTransition x :=
  div_nonneg (expNegInvGlue.nonneg _) (pos_denom x).le
theorem lt_one_of_lt_one (h : x < 1) : smoothTransition x < 1 :=
  (div_lt_one <| pos_denom x).2 <| lt_add_of_pos_right _ <| pos_of_pos <| sub_pos.2 h
theorem pos_of_pos (h : 0 < x) : 0 < smoothTransition x :=
  div_pos (expNegInvGlue.pos_of_pos h) (pos_denom x)
protected theorem contDiff {n : ℕ∞} : ContDiff ℝ n smoothTransition :=
  expNegInvGlue.contDiff.div
    (expNegInvGlue.contDiff.add <| expNegInvGlue.contDiff.comp <| contDiff_const.sub contDiff_id)
    fun x => (pos_denom x).ne'
protected theorem contDiffAt {x : ℝ} {n : ℕ∞} : ContDiffAt ℝ n smoothTransition x :=
  smoothTransition.contDiff.contDiffAt
protected theorem continuous : Continuous smoothTransition :=
  (@smoothTransition.contDiff 0).continuous
protected theorem continuousAt : ContinuousAt smoothTransition x :=
  smoothTransition.continuous.continuousAt
end smoothTransition
end Real