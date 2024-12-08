import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Average
open MeasureTheory Set TopologicalSpace
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
notation3 "⨍ "(...)" in "a".."b",
  "r:60:(scoped f => average (Measure.restrict volume (uIoc a b)) f) => r
theorem interval_average_symm (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = ⨍ x in b..a, f x := by
  rw [setAverage_eq, setAverage_eq, uIoc_comm]
theorem interval_average_eq (f : ℝ → E) (a b : ℝ) :
    (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x := by
  rcases le_or_lt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_Ioc, intervalIntegral.integral_of_le h,
      ENNReal.toReal_ofReal (sub_nonneg.2 h)]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_Ioc, intervalIntegral.integral_of_ge h.le,
      ENNReal.toReal_ofReal (sub_nonneg.2 h.le), smul_neg, ← neg_smul, ← inv_neg, neg_sub]
theorem interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) :
    (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) := by
  rw [interval_average_eq, smul_eq_mul, div_eq_inv_mul]