import Mathlib.Probability.Notation
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open scoped ENNReal NNReal
open MeasureTheory Real Set Filter Topology
namespace ProbabilityTheory
variable {t r x : ℝ}
section ParetoPDF
noncomputable def paretoPDFReal (t r x : ℝ) : ℝ :=
  if t ≤ x then r * t ^ r * x ^ (-(r + 1)) else 0
noncomputable def paretoPDF (t r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (paretoPDFReal t r x)
lemma paretoPDF_eq (t r x : ℝ) :
    paretoPDF t r x = ENNReal.ofReal (if t ≤ x then r * t ^ r * x ^ (-(r + 1)) else 0) := rfl
lemma paretoPDF_of_lt (hx : x < t) : paretoPDF t r x = 0 := by
  simp only [paretoPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]
lemma paretoPDF_of_le (hx : t ≤ x) :
    paretoPDF t r x = ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1))) := by
  simp only [paretoPDF_eq, if_pos hx]
lemma lintegral_paretoPDF_of_le (hx : x ≤ t) :
    ∫⁻ y in Iio x, paretoPDF t r y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · simp only [paretoPDF_eq, ge_iff_le, ENNReal.ofReal_eq_zero]
    filter_upwards with a (_ : a < _)
    rw [if_neg (by linarith)]
@[measurability, fun_prop]
lemma measurable_paretoPDFReal (t r : ℝ) : Measurable (paretoPDFReal t r) :=
  Measurable.ite measurableSet_Ici ((measurable_id.pow_const _).const_mul _) measurable_const
@[measurability]
lemma stronglyMeasurable_paretoPDFReal (t r : ℝ) :
    StronglyMeasurable (paretoPDFReal t r) :=
  (measurable_paretoPDFReal t r).stronglyMeasurable
lemma paretoPDFReal_pos (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x) :
    0 < paretoPDFReal t r x := by
  rw [paretoPDFReal, if_pos hx]
  have _ : 0 < x := by linarith
  positivity
lemma paretoPDFReal_nonneg (ht : 0 ≤ t) (hr : 0 ≤ r) (x : ℝ) :
    0 ≤ paretoPDFReal t r x := by
  unfold paretoPDFReal
  split_ifs with h
  · cases le_iff_eq_or_lt.1 ht with
    | inl ht0 =>
      rw [← ht0] at h
      positivity
    | inr htp =>
      have := lt_of_lt_of_le htp h
      positivity
  · positivity
open Measure
@[simp]
lemma lintegral_paretoPDF_eq_one (ht : 0 < t) (hr : 0 < r) :
    ∫⁻ x, paretoPDF t r x = 1 := by
  have leftSide : ∫⁻ x in Iio t, paretoPDF t r x = 0 := lintegral_paretoPDF_of_le (le_refl t)
  have rightSide : ∫⁻ x in Ici t, paretoPDF t r x =
      ∫⁻ x in Ici t, ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1))) :=
    setLIntegral_congr_fun measurableSet_Ici (ae_of_all _ (fun _ ↦ paretoPDF_of_le))
  rw [← ENNReal.toReal_eq_one_iff, ← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftSide, rightSide, add_zero, ← integral_eq_lintegral_of_nonneg_ae]
  · rw [integral_Ici_eq_integral_Ioi, integral_mul_left, integral_Ioi_rpow_of_lt _ ht]
    · field_simp [hr]
      rw [mul_assoc, ← rpow_add ht]
      simp
    linarith
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    refine ae_of_all _ fun x (hx : t ≤ x) ↦ ?_
    have := lt_of_lt_of_le ht hx
    positivity
  · apply (measurable_paretoPDFReal t r).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ici).mpr <| ae_of_all _ fun x (hx : t ≤ x) ↦ ?_
    simp_rw [paretoPDFReal, eq_true_intro hx, ite_true]
end ParetoPDF
open MeasureTheory
noncomputable def paretoMeasure (t r : ℝ) : Measure ℝ :=
  volume.withDensity (paretoPDF t r)
lemma isProbabilityMeasure_paretoMeasure (ht : 0 < t) (hr : 0 < r) :
    IsProbabilityMeasure (paretoMeasure t r) where
  measure_univ := by simp [paretoMeasure, lintegral_paretoPDF_eq_one ht hr]
section ParetoCDF
lemma paretoCDFReal_eq_integral (ht : 0 < t) (hr : 0 < r) (x : ℝ) :
    cdf (paretoMeasure t r) x = ∫ x in Iic x, paretoPDFReal t r x := by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_toReal, paretoMeasure, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun _ ↦ by simp only [Pi.zero_apply, paretoPDFReal_nonneg ht.le hr.le]
  · exact (measurable_paretoPDFReal t r).aestronglyMeasurable.restrict
lemma paretoCDFReal_eq_lintegral (ht : 0 < t) (hr : 0 < r) (x : ℝ) :
    cdf (paretoMeasure t r) x = ENNReal.toReal (∫⁻ x in Iic x, paretoPDF t r x) := by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_toReal, paretoMeasure, withDensity_apply _ measurableSet_Iic]
end ParetoCDF
end ProbabilityTheory