import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner
namespace PMF
open MeasureTheory ENNReal TopologicalSpace
section General
variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
theorem integral_eq_tsum (p : PMF α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a := calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply integral_countable f p.support_countable
    rwa [IntegrableOn, restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal • f a := by
    congr with x; congr 2
    apply PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)
  _ = ∑' a, (p a).toReal • f a :=
    tsum_subtype_eq_of_support_subset <| calc
      (fun a ↦ (p a).toReal • f a).support ⊆ (fun a ↦ (p a).toReal).support :=
        Function.support_smul_subset_left _ _
      _ ⊆ support p := fun x h1 h2 => h1 (by simp [h2])
theorem integral_eq_sum [Fintype α] (p : PMF α) (f : α → E) :
    ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a := by
  rw [integral_fintype _ .of_finite]
  congr with x; congr 2
  exact PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)
end General
theorem bernoulli_expectation {p : ℝ≥0∞} (h : p ≤ 1) :
    ∫ b, cond b 1 0 ∂((bernoulli p h).toMeasure) = p.toReal := by simp [integral_eq_sum]
end PMF