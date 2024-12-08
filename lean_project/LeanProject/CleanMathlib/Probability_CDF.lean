import Mathlib.Probability.Kernel.Disintegration.CondCDF
open MeasureTheory Set Filter
open scoped Topology
namespace ProbabilityTheory
noncomputable
def cdf (μ : Measure ℝ) : StieltjesFunction :=
  condCDF ((Measure.dirac Unit.unit).prod μ) Unit.unit
section ExplicitMeasureArg
variable (μ : Measure ℝ)
lemma cdf_nonneg (x : ℝ) : 0 ≤ cdf μ x := condCDF_nonneg _ _ _
lemma cdf_le_one (x : ℝ) : cdf μ x ≤ 1 := condCDF_le_one _ _ _
lemma monotone_cdf : Monotone (cdf μ) := (condCDF _ _).mono
lemma tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0) := tendsto_condCDF_atBot _ _
lemma tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1) := tendsto_condCDF_atTop _ _
lemma ofReal_cdf [IsProbabilityMeasure μ] (x : ℝ) : ENNReal.ofReal (cdf μ x) = μ (Iic x) := by
  have h := lintegral_condCDF ((Measure.dirac Unit.unit).prod μ) x
  simpa only [MeasureTheory.Measure.fst_prod, Measure.prod_prod, measure_univ, one_mul,
    lintegral_dirac] using h
lemma cdf_eq_toReal [IsProbabilityMeasure μ] (x : ℝ) : cdf μ x = (μ (Iic x)).toReal := by
  rw [← ofReal_cdf μ x, ENNReal.toReal_ofReal (cdf_nonneg μ x)]
instance instIsProbabilityMeasurecdf : IsProbabilityMeasure (cdf μ).measure := by
  constructor
  simp only [StieltjesFunction.measure_univ _ (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ), sub_zero,
    ENNReal.ofReal_one]
lemma measure_cdf [IsProbabilityMeasure μ] : (cdf μ).measure = μ := by
  refine Measure.ext_of_Iic (cdf μ).measure μ (fun a ↦ ?_)
  rw [StieltjesFunction.measure_Iic _ (tendsto_cdf_atBot μ), sub_zero, ofReal_cdf]
end ExplicitMeasureArg
lemma cdf_measure_stieltjesFunction (f : StieltjesFunction) (hf0 : Tendsto f atBot (𝓝 0))
    (hf1 : Tendsto f atTop (𝓝 1)) :
    cdf f.measure = f := by
  refine (cdf f.measure).eq_of_measure_of_tendsto_atBot f ?_ (tendsto_cdf_atBot _) hf0
  have h_prob : IsProbabilityMeasure f.measure :=
    ⟨by rw [f.measure_univ hf0 hf1, sub_zero, ENNReal.ofReal_one]⟩
  exact measure_cdf f.measure
end ProbabilityTheory
open ProbabilityTheory
lemma MeasureTheory.Measure.eq_of_cdf (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : cdf μ = cdf ν) : μ = ν := by
  rw [← measure_cdf μ, ← measure_cdf ν, h]
@[simp] lemma MeasureTheory.Measure.cdf_eq_iff (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    cdf μ = cdf ν ↔ μ = ν :=
⟨MeasureTheory.Measure.eq_of_cdf μ ν, fun h ↦ by rw [h]⟩