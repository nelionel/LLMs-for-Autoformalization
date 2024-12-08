import Mathlib.Algebra.Polynomial.AlgebraMap
variable {K : Type*} [Field K] (R : Subring K)
open Polynomial
open scoped Polynomial
def Polynomial.int (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R) : R[X] where
  toFinsupp :=
  { support := P.support
    toFun := fun n => ⟨P.coeff n, hP n⟩
    mem_support_toFun := fun n => by
      rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff] }
namespace Polynomial
variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)
@[simp]
theorem int_coeff_eq  (n : ℕ) : ↑((P.int R hP).coeff n) = P.coeff n := rfl
@[simp]
theorem int_leadingCoeff_eq : ↑(P.int R hP).leadingCoeff = P.leadingCoeff := rfl
@[simp]
theorem int_monic_iff : (P.int R hP).Monic ↔ P.Monic := by
  rw [Monic, Monic, ← int_leadingCoeff_eq, OneMemClass.coe_eq_one]
@[simp]
theorem int_natDegree : (P.int R hP).natDegree = P.natDegree := rfl
variable {L : Type*} [Field L] [Algebra K L]
@[simp]
theorem int_eval₂_eq (x : L) :
    eval₂ (algebraMap R L) x (P.int R hP) = aeval x P := by
  rw [aeval_eq_sum_range, eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)
end Polynomial