import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Interval
noncomputable section
open Finset (antidiagonal mem_antidiagonal)
namespace MvPowerSeries
open Finsupp
variable {σ R : Type*}
section Trunc
variable [CommSemiring R] (n : σ →₀ ℕ)
def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.Iio n, MvPolynomial.monomial m (coeff R m φ)
theorem coeff_truncFun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical
  simp [truncFun, MvPolynomial.coeff_sum]
variable (R)
def trunc : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun n
  map_zero' := by
    classical
    ext
    simp [coeff_truncFun]
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun, MvPolynomial.coeff_add]
    split_ifs
    · rw [map_add]
    · rw [zero_add]
variable {R}
theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical simp [trunc, coeff_truncFun]
@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m => by
    classical
    rw [coeff_trunc, coeff_one]
    split_ifs with H H'
    · subst m
      simp
    · symm
      rw [MvPolynomial.coeff_one]
      exact if_neg (Ne.symm H')
    · symm
      rw [MvPolynomial.coeff_one]
      refine if_neg ?_
      rintro rfl
      apply H
      exact Ne.bot_lt hnn
@[simp]
theorem trunc_c (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C σ R a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m => by
    classical
    rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first |rfl|try simp_all only [ne_eq, not_true_eq_false]
    exfalso; apply H; subst m; exact Ne.bot_lt hnn
end Trunc
end MvPowerSeries
end