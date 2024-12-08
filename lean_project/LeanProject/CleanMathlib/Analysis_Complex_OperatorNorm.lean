import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Data.Complex.Determinant
open ContinuousLinearMap
namespace Complex
@[simp]
theorem det_conjLIE : LinearMap.det (conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 :=
  det_conjAe
@[simp]
theorem linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe
@[simp]
theorem reCLM_norm : ‖reCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reCLM 1‖ := by simp
      _ ≤ ‖reCLM‖ := unit_le_opNorm _ _ (by simp)
@[simp]
theorem reCLM_nnnorm : ‖reCLM‖₊ = 1 :=
  Subtype.ext reCLM_norm
@[simp]
theorem imCLM_norm : ‖imCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imCLM I‖ := by simp
      _ ≤ ‖imCLM‖ := unit_le_opNorm _ _ (by simp)
@[simp]
theorem imCLM_nnnorm : ‖imCLM‖₊ = 1 :=
  Subtype.ext imCLM_norm
@[simp]
theorem conjCLE_norm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLIE.toLinearIsometry.norm_toContinuousLinearMap
@[simp]
theorem conjCLE_nnorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCLE_norm
@[simp]
theorem ofRealCLM_norm : ‖ofRealCLM‖ = 1 :=
  ofRealLI.norm_toContinuousLinearMap
@[simp]
theorem ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1 :=
  Subtype.ext <| ofRealCLM_norm
end Complex