import Mathlib.Algebra.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finsupp
universe u
open Cardinal Polynomial
open Cardinal
namespace Polynomial
@[simp]
theorem cardinalMk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : #(R[X]) = max #R ℵ₀ :=
  (toFinsuppIso R).toEquiv.cardinal_eq.trans <| by
    rw [AddMonoidAlgebra, mk_finsupp_lift_of_infinite, lift_uzero, max_comm]
    rfl
@[deprecated (since := "2024-11-10")] alias cardinal_mk_eq_max := cardinalMk_eq_max
theorem cardinalMk_le_max {R : Type u} [Semiring R] : #(R[X]) ≤ max #R ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  · exact cardinalMk_eq_max.le
@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_max := cardinalMk_le_max
end Polynomial