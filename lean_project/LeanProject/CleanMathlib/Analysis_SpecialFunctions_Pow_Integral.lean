import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.Layercake
open Set
namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f)
  (f_mble : AEMeasurable f μ) {p : ℝ} (p_pos : 0 < p)
include f_nn f_mble p_pos
section Layercake
include f_nn f_mble p_pos in
theorem lintegral_rpow_eq_lintegral_meas_le_mul :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : ∀ x : ℝ, ∫ t : ℝ in (0)..x, t ^ (p - 1) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : ℝ => t ^ (p - 1)
  have g_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    intro t t_pos
    exact Real.rpow_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t := fun _ _ =>
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key, ← lintegral_const_mul'' (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le, mul_div_cancel₀ (f ω ^ p) p_pos.ne.symm]
  · have aux := (@measurable_const ℝ α (by infer_instance) (by infer_instance) p).aemeasurable
                  (μ := μ)
    exact (Measurable.ennreal_ofReal (hf := measurable_id)).comp_aemeasurable
      ((f_mble.pow aux).div_const p)
end Layercake
section LayercakeLT
include f_nn f_mble p_pos in
theorem lintegral_rpow_eq_lintegral_meas_lt_mul :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f]
    with t ht
  rw [ht]
end LayercakeLT
end MeasureTheory