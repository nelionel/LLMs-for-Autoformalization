import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Mathlib.RingTheory.Polynomial.Chebyshev
namespace Polynomial.Chebyshev
open Polynomial
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
@[simp]
theorem aeval_T (x : A) (n : ℤ) : aeval x (T R n) = (T A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_T]
@[simp]
theorem aeval_U (x : A) (n : ℤ) : aeval x (U R n) = (U A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_U]
@[simp]
theorem algebraMap_eval_T (x : R) (n : ℤ) :
    algebraMap R A ((T R n).eval x) = (T A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_T]
@[simp]
theorem algebraMap_eval_U (x : R) (n : ℤ) :
    algebraMap R A ((U R n).eval x) = (U A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_U]
@[simp, norm_cast]
theorem complex_ofReal_eval_T : ∀ (x : ℝ) n, (((T ℝ n).eval x : ℝ) : ℂ) = (T ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_T ℝ ℂ _ _ _
@[simp, norm_cast]
theorem complex_ofReal_eval_U : ∀ (x : ℝ) n, (((U ℝ n).eval x : ℝ) : ℂ) = (U ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_U ℝ ℂ _ _ _
section Complex
open Complex
variable (θ : ℂ)
@[simp]
theorem T_complex_cos (n : ℤ) : (T ℂ n).eval (cos θ) = cos (n * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add,
      cos_add_cos]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add',
      cos_add_cos]
    push_cast
    ring_nf
@[simp]
theorem U_complex_cos (n : ℤ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp [one_add_one_eq_two, sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    simp only [U_add_two, add_sub_cancel_right, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add, sin_add_sin]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, add_sub_cancel_right, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add', sin_add_sin]
    push_cast
    ring_nf
@[simp]
theorem C_two_mul_complex_cos (n : ℤ) : (C ℂ n).eval (2 * cos θ) = 2 * cos (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]
@[simp]
theorem S_two_mul_complex_cos (n : ℤ) : (S ℂ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]
end Complex
section Real
open Real
variable (θ : ℝ) (n : ℤ)
@[simp]
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) := mod_cast T_complex_cos θ n
@[simp]
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast U_complex_cos θ n
@[simp]
theorem C_two_mul_real_cos : (C ℝ n).eval (2 * cos θ) = 2 * cos (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]
@[simp]
theorem S_two_mul_real_cos : (S ℝ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]
end Real
end Polynomial.Chebyshev