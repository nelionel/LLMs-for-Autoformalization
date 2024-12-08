import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.RingTheory.Coprime.Basic
noncomputable section
open scoped Polynomial
namespace Polynomial
variable {R : Type*} [CommRing R]
def wronskian (a b : R[X]) : R[X] :=
  a * (derivative b) - (derivative a) * b
variable (R) in
def wronskianBilin : R[X] →ₗ[R] R[X] →ₗ[R] R[X] :=
  (LinearMap.mul R R[X]).compl₂ derivative - (LinearMap.mul R R[X]).comp derivative
@[simp]
theorem wronskianBilin_apply (a b : R[X]) : wronskianBilin R a b = wronskian a b := rfl
@[simp]
theorem wronskian_zero_left (a : R[X]) : wronskian 0 a = 0 := by
  rw [← wronskianBilin_apply 0 a, map_zero]; rfl
@[simp]
theorem wronskian_zero_right (a : R[X]) : wronskian a 0 = 0 := (wronskianBilin R a).map_zero
theorem wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b :=
  LinearMap.map_neg₂ (wronskianBilin R) a b
theorem wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b :=
  (wronskianBilin R a).map_neg b
theorem wronskian_add_right (a b c : R[X]) : wronskian a (b + c) = wronskian a b + wronskian a c :=
  (wronskianBilin R a).map_add b c
theorem wronskian_add_left (a b c : R[X]) : wronskian (a + b) c = wronskian a c + wronskian b c :=
  (wronskianBilin R).map_add₂ a b c
theorem wronskian_self_eq_zero (a : R[X]) : wronskian a a = 0 := by
  rw [wronskian, mul_comm, sub_self]
theorem isAlt_wronskianBilin : (wronskianBilin R).IsAlt := wronskian_self_eq_zero
theorem wronskian_neg_eq (a b : R[X]) : -wronskian a b = wronskian b a :=
  LinearMap.IsAlt.neg isAlt_wronskianBilin a b
theorem wronskian_eq_of_sum_zero {a b c : R[X]} (hAdd : a + b + c = 0) :
    wronskian a b = wronskian b c := isAlt_wronskianBilin.eq_of_add_add_eq_zero hAdd
theorem degree_wronskian_lt_add {a b : R[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (wronskian a b).degree < a.degree + b.degree := by
  calc
    (wronskian a b).degree ≤ max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]
      constructor
      case left =>
        apply lt_of_le_of_lt
        · exact degree_mul_le a (derivative b)
        · rw [← Polynomial.degree_ne_bot] at ha
          rw [WithBot.add_lt_add_iff_left ha]
          exact Polynomial.degree_derivative_lt hb
      case right =>
        apply lt_of_le_of_lt
        · exact degree_mul_le (derivative a) b
        · rw [← Polynomial.degree_ne_bot] at hb
          rw [WithBot.add_lt_add_iff_right hb]
          exact Polynomial.degree_derivative_lt ha
theorem natDegree_wronskian_lt_add {a b : R[X]} (hw : wronskian a b ≠ 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree := by
  have ha : a ≠ 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b ≠ 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  rw [← WithBot.coe_lt_coe, WithBot.coe_add]
  convert ← degree_wronskian_lt_add ha hb
  · exact Polynomial.degree_eq_natDegree hw
  · exact Polynomial.degree_eq_natDegree ha
  · exact Polynomial.degree_eq_natDegree hb
theorem _root_.IsCoprime.wronskian_eq_zero_iff
    [NoZeroDivisors R] {a b : R[X]} (hc : IsCoprime a b) :
    wronskian a b = 0 ↔ derivative a = 0 ∧ derivative b = 0 where
  mp hw := by
    rw [wronskian, sub_eq_iff_eq_add, zero_add] at hw
    constructor
    · rw [← dvd_derivative_iff]
      apply hc.dvd_of_dvd_mul_right
      rw [← hw]; exact dvd_mul_right _ _
    · rw [← dvd_derivative_iff]
      apply hc.symm.dvd_of_dvd_mul_left
      rw [hw]; exact dvd_mul_left _ _
  mpr hdab := by
    cases' hdab with hda hdb
    rw [wronskian]
    rw [hda, hdb]; simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, sub_self]
@[deprecated (since := "2024-11-06")]
alias IsCoprime.wronskian_eq_zero_iff := IsCoprime.wronskian_eq_zero_iff
end Polynomial