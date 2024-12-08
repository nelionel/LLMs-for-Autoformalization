import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Valuation.Basic
open Module minpoly Polynomial
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (L : Type*) [Field L] [Algebra K L]
namespace Valuation
@[simp]
theorem coeff_zero_minpoly (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = v x := by
  rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg]
variable {L}
theorem pow_coeff_zero_ne_zero_of_unit [FiniteDimensional K L] (x : L) (hx : IsUnit x):
    v ((minpoly K x).coeff 0) ^ (finrank K L / (minpoly K x).natDegree) ≠ (0 : Γ₀) := by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hx₀ : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hdeg := Nat.div_pos (natDegree_le x) (natDegree_pos hx₀)
  rw [ne_eq, pow_eq_zero_iff hdeg.ne.symm, Valuation.zero_iff]
  exact coeff_zero_ne_zero hx₀ hx.ne_zero
end Valuation