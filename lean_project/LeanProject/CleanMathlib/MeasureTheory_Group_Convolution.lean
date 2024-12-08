import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
namespace MeasureTheory
namespace Measure
variable {M : Type*} [Monoid M] [MeasurableSpace M]
@[to_additive conv "Additive convolution of measures."]
noncomputable def mconv (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.Measure.mconv
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.Measure.conv
@[to_additive (attr := simp)]
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (Measure.dirac 1) ∗ μ = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.dirac_prod, map_map (by fun_prop)]
  · simp only [Function.comp_def, one_mul, map_id']
  fun_prop
@[to_additive (attr := simp)]
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ (Measure.dirac 1) = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.prod_dirac, map_map (by fun_prop)]
  · simp only [Function.comp_def, mul_one, map_id']
  fun_prop
@[to_additive (attr := simp) conv_zero]
theorem mconv_zero (μ : Measure M) : (0 : Measure M) ∗ μ = (0 : Measure M) := by
  unfold mconv
  simp
@[to_additive (attr := simp) zero_conv]
theorem zero_mconv (μ : Measure M) : μ ∗ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp
@[to_additive conv_add]
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ (ν + ρ) = μ ∗ ν + μ ∗ ρ := by
  unfold mconv
  rw [prod_add, map_add]
  fun_prop
@[to_additive add_conv]
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ ρ = μ ∗ ρ + ν ∗ ρ := by
  unfold mconv
  rw [add_prod, map_add]
  fun_prop
@[to_additive conv_comm]
theorem mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ ν = ν ∗ μ := by
  unfold mconv
  rw [← prod_swap, map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop
@[to_additive sfinite_conv_of_sfinite]
instance sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] :
    SFinite (μ ∗ ν) := inferInstanceAs <| SFinite ((μ.prod ν).map fun (x : M × M) ↦ x.1 * x.2)
@[to_additive finite_of_finite_conv]
instance finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ ν) := by
  have h : (μ ∗ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact {measure_univ_lt_top := h}
@[to_additive probabilitymeasure_of_probabilitymeasures_conv]
instance probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measure M)
    [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ ν) :=
  MeasureTheory.isProbabilityMeasure_map (by fun_prop)
end Measure
end MeasureTheory