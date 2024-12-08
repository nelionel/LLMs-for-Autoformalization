import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content
noncomputable section
universe u
variable {K : Type u}
namespace RatFunc
section Eval
open scoped Classical
open scoped nonZeroDivisors Polynomial
open RatFunc
section Domain
variable [CommRing K] [IsDomain K]
def C : K →+* RatFunc K := algebraMap _ _
@[simp]
theorem algebraMap_eq_C : algebraMap K (RatFunc K) = C :=
  rfl
@[simp]
theorem algebraMap_C (a : K) : algebraMap K[X] (RatFunc K) (Polynomial.C a) = C a :=
  rfl
@[simp]
theorem algebraMap_comp_C : (algebraMap K[X] (RatFunc K)).comp Polynomial.C = C :=
  rfl
theorem smul_eq_C_mul (r : K) (x : RatFunc K) : r • x = C r * x := by
  rw [Algebra.smul_def, algebraMap_eq_C]
def X : RatFunc K :=
  algebraMap K[X] (RatFunc K) Polynomial.X
@[simp]
theorem algebraMap_X : algebraMap K[X] (RatFunc K) Polynomial.X = X :=
  rfl
end Domain
section Field
variable [Field K]
@[simp]
theorem num_C (c : K) : num (C c) = Polynomial.C c :=
  num_algebraMap _
@[simp]
theorem denom_C (c : K) : denom (C c) = 1 :=
  denom_algebraMap _
@[simp]
theorem num_X : num (X : RatFunc K) = Polynomial.X :=
  num_algebraMap _
@[simp]
theorem denom_X : denom (X : RatFunc K) = 1 :=
  denom_algebraMap _
theorem X_ne_zero : (X : RatFunc K) ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
variable {L : Type u} [Field L]
def eval (f : K →+* L) (a : L) (p : RatFunc K) : L :=
  (num p).eval₂ f a / (denom p).eval₂ f a
variable {f : K →+* L} {a : L}
theorem eval_eq_zero_of_eval₂_denom_eq_zero {x : RatFunc K}
    (h : Polynomial.eval₂ f a (denom x) = 0) : eval f a x = 0 := by rw [eval, h, div_zero]
theorem eval₂_denom_ne_zero {x : RatFunc K} (h : eval f a x ≠ 0) :
    Polynomial.eval₂ f a (denom x) ≠ 0 :=
  mt eval_eq_zero_of_eval₂_denom_eq_zero h
variable (f a)
@[simp]
theorem eval_C {c : K} : eval f a (C c) = f c := by simp [eval]
@[simp]
theorem eval_X : eval f a X = a := by simp [eval]
@[simp]
theorem eval_zero : eval f a 0 = 0 := by simp [eval]
@[simp]
theorem eval_one : eval f a 1 = 1 := by simp [eval]
@[simp]
theorem eval_algebraMap {S : Type*} [CommSemiring S] [Algebra S K[X]] (p : S) :
    eval f a (algebraMap _ _ p) = (algebraMap _ K[X] p).eval₂ f a := by
  simp [eval, IsScalarTower.algebraMap_apply S K[X] (RatFunc K)]
theorem eval_add {x y : RatFunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x + y) = eval f a x + eval f a y := by
  unfold eval
  by_cases hxy : Polynomial.eval₂ f a (denom (x + y)) = 0
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_add_dvd x y) hxy
    rw [Polynomial.eval₂_mul] at this
    cases mul_eq_zero.mp this <;> contradiction
  rw [div_add_div _ _ hx hy, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  simp only [← Polynomial.eval₂_mul, ← Polynomial.eval₂_add]
  congr 1
  apply num_denom_add
theorem eval_mul {x y : RatFunc K} (hx : Polynomial.eval₂ f a (denom x) ≠ 0)
    (hy : Polynomial.eval₂ f a (denom y) ≠ 0) : eval f a (x * y) = eval f a x * eval f a y := by
  unfold eval
  by_cases hxy : Polynomial.eval₂ f a (denom (x * y)) = 0
  · have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_mul_dvd x y) hxy
    rw [Polynomial.eval₂_mul] at this
    cases mul_eq_zero.mp this <;> contradiction
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm, ←
    div_eq_mul_inv, div_eq_iff hxy]
  repeat' rw [← Polynomial.eval₂_mul]
  congr 1
  apply num_denom_mul
end Field
end Eval
end RatFunc
section AdicValuation
variable (K : Type*) [Field K]
namespace Polynomial
open IsDedekindDomain.HeightOneSpectrum
def idealX : IsDedekindDomain.HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {X}
  isPrime := by rw [Ideal.span_singleton_prime]; exacts [Polynomial.prime_X, Polynomial.X_ne_zero]
  ne_bot  := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact Polynomial.X_ne_zero
@[simp]
theorem idealX_span : (idealX K).asIdeal = Ideal.span {X} := rfl
@[simp]
theorem valuation_X_eq_neg_one :
    (idealX K).valuation (RatFunc.X : RatFunc K) = Multiplicative.ofAdd (-1 : ℤ) := by
  rw [← RatFunc.algebraMap_X, valuation_of_algebraMap, intValuation_singleton]
  · exact Polynomial.X_ne_zero
  · exact idealX_span K
theorem valuation_of_mk (f : Polynomial K) {g : Polynomial K} (hg : g ≠ 0) :
    (Polynomial.idealX K).valuation (RatFunc.mk f g) =
      (Polynomial.idealX K).intValuation f / (Polynomial.idealX K).intValuation g := by
  simp only [RatFunc.mk_eq_mk' _ hg, valuation_of_mk']
end Polynomial
namespace RatFunc
open scoped Multiplicative
open Polynomial
instance : Valued (RatFunc K) ℤₘ₀ := Valued.mk' (idealX K).valuation
@[simp]
theorem WithZero.valued_def {x : RatFunc K} :
    @Valued.v (RatFunc K) _ _ _ _ x = (idealX K).valuation x := rfl
end RatFunc
end AdicValuation