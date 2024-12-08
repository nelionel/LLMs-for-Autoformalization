import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.NormedSpace.Pointwise
open Metric
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
theorem RCLike.norm_coe_norm {z : E} : ‖(‖z‖ : 𝕜)‖ = ‖z‖ := by simp
variable [NormedSpace 𝕜 E]
@[simp]
theorem norm_smul_inv_norm {x : E} (hx : x ≠ 0) : ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 := by
  have : ‖x‖ ≠ 0 := by simp [hx]
  field_simp [norm_smul]
theorem norm_smul_inv_norm' {r : ℝ} (r_nonneg : 0 ≤ r) {x : E} (hx : x ≠ 0) :
    ‖((r : 𝕜) * (‖x‖ : 𝕜)⁻¹) • x‖ = r := by
  have : ‖x‖ ≠ 0 := by simp [hx]
  field_simp [norm_smul, r_nonneg, rclike_simps]
theorem LinearMap.bound_of_sphere_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀ z ∈ sphere (0 : E) r, ‖f z‖ ≤ c) (z : E) : ‖f z‖ ≤ c / r * ‖z‖ := by
  by_cases z_zero : z = 0
  · rw [z_zero]
    simp only [LinearMap.map_zero, norm_zero, mul_zero]
    exact le_rfl
  set z₁ := ((r : 𝕜) * (‖z‖ : 𝕜)⁻¹) • z with hz₁
  have norm_f_z₁ : ‖f z₁‖ ≤ c := by
    apply h
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm' r_pos.le z_zero
  have r_ne_zero : (r : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr r_pos.ne'
  have eq : f z = ‖z‖ / r * f z₁ := by
    rw [hz₁, LinearMap.map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, div_mul_cancel₀ _ r_ne_zero, mul_inv_cancel₀, one_mul]
    simp only [z_zero, RCLike.ofReal_eq_zero, norm_eq_zero, Ne, not_false_iff]
  rw [eq, norm_mul, norm_div, RCLike.norm_coe_norm, RCLike.norm_of_nonneg r_pos.le,
    div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm]
  apply div_le_div₀ _ _ r_pos rfl.ge
  · exact mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z)
  apply mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁)
theorem LinearMap.bound_of_ball_bound' {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀ z ∈ closedBall (0 : E) r, ‖f z‖ ≤ c) (z : E) : ‖f z‖ ≤ c / r * ‖z‖ :=
  f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z
theorem ContinuousLinearMap.opNorm_bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ)
    (f : E →L[𝕜] 𝕜) (h : ∀ z ∈ closedBall (0 : E) r, ‖f z‖ ≤ c) : ‖f‖ ≤ c / r := by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg _ r_pos.le
    exact
      (norm_nonneg _).trans
        (h 0 (by simp only [norm_zero, mem_closedBall, dist_zero_left, r_pos.le]))
  apply LinearMap.bound_of_ball_bound' r_pos
  exact fun z hz => h z hz
@[deprecated (since := "2024-02-02")]
alias ContinuousLinearMap.op_norm_bound_of_ball_bound :=
  ContinuousLinearMap.opNorm_bound_of_ball_bound
variable (𝕜)
include 𝕜 in
theorem NormedSpace.sphere_nonempty_rclike [Nontrivial E] {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (sphere (0 : E) r) :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  (NormedSpace.sphere_nonempty.mpr hr).coe_sort