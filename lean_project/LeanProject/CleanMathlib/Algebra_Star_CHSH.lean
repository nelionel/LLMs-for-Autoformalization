import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Polyrith
universe u
structure IsCHSHTuple {R} [Monoid R] [StarMul R] (A₀ A₁ B₀ B₁ : R) : Prop where
  A₀_inv : A₀ ^ 2 = 1
  A₁_inv : A₁ ^ 2 = 1
  B₀_inv : B₀ ^ 2 = 1
  B₁_inv : B₁ ^ 2 = 1
  A₀_sa : star A₀ = A₀
  A₁_sa : star A₁ = A₁
  B₀_sa : star B₀ = B₀
  B₁_sa : star B₁ = B₁
  A₀B₀_commutes : A₀ * B₀ = B₀ * A₀
  A₀B₁_commutes : A₀ * B₁ = B₁ * A₀
  A₁B₀_commutes : A₁ * B₀ = B₀ * A₁
  A₁B₁_commutes : A₁ * B₁ = B₁ * A₁
variable {R : Type u}
theorem CHSH_id [CommRing R] {A₀ A₁ B₀ B₁ : R} (A₀_inv : A₀ ^ 2 = 1) (A₁_inv : A₁ ^ 2 = 1)
    (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1) :
    (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) =
      4 * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) := by
  linear_combination
    (2 * B₀ * B₁ + 2) * A₀_inv + (B₀ ^ 2 - 2 * B₀ * B₁ + B₁ ^ 2) * A₁_inv +
        (A₀ ^ 2 + 2 * A₀ * A₁ + 1) * B₀_inv +
      (A₀ ^ 2 - 2 * A₀ * A₁ + 1) * B₁_inv
theorem CHSH_inequality_of_comm [OrderedCommRing R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R]
    [OrderedSMul ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 := by
  let P := 2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁
  have i₁ : 0 ≤ P := by
    have idem : P * P = 4 * P := CHSH_id T.A₀_inv T.A₁_inv T.B₀_inv T.B₁_inv
    have idem' : P = (1 / 4 : ℝ) • (P * P) := by
      have h : 4 * P = (4 : ℝ) • P := by simp [map_ofNat, Algebra.smul_def]
      rw [idem, h, ← mul_smul]
      norm_num
    have sa : star P = P := by
      dsimp [P]
      simp only [star_add, star_sub, star_mul, star_ofNat, star_one, T.A₀_sa, T.A₁_sa, T.B₀_sa,
        T.B₁_sa, mul_comm B₀, mul_comm B₁]
    simpa only [← idem', sa]
      using smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (star_mul_self_nonneg P)
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add] using i₁
namespace TsirelsonInequality
theorem tsirelson_inequality_aux : √2 * √2 ^ 3 = √2 * (2 * (√2)⁻¹ + 4 * ((√2)⁻¹ * 2⁻¹)) := by
  ring_nf
  rw [mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (show (2 : ℝ) > 0 by norm_num)))]
  convert congr_arg (· ^ 2) (@Real.sq_sqrt 2 (by norm_num)) using 1 <;>
    (try simp only [← pow_mul]) <;> norm_num
theorem sqrt_two_inv_mul_self : (√2)⁻¹ * (√2)⁻¹ = (2⁻¹ : ℝ) := by
  rw [← mul_inv]
  norm_num
end TsirelsonInequality
open TsirelsonInequality
theorem tsirelson_inequality [OrderedRing R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R]
    [OrderedSMul ℝ R] [StarModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • (1 : R) := by
  have M : ∀ (m : ℤ) (a : ℝ) (x : R), m • a • x = ((m : ℝ) * a) • x := fun m a x => by
    rw [← Int.cast_smul_eq_zsmul ℝ, ← mul_smul]
  let P := (√2)⁻¹ • (A₁ + A₀) - B₀
  let Q := (√2)⁻¹ • (A₁ - A₀) + B₁
  have w : √2 ^ 3 • (1 : R) - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁ = (√2)⁻¹ • (P ^ 2 + Q ^ 2) := by
    dsimp [P, Q]
    simp only [sq, sub_mul, mul_sub, add_mul, mul_add, smul_add, smul_sub]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, sqrt_two_inv_mul_self]
    simp only [← sq, T.A₀_inv, T.A₁_inv, T.B₀_inv, T.B₁_inv]
    simp only [← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
    abel_nf
    simp only [M]
    simp only [neg_mul, one_mul, mul_inv_cancel_of_invertible, Int.cast_one, add_assoc, add_comm,
      add_left_comm, one_smul, Int.cast_neg, neg_smul, Int.cast_ofNat]
    simp only [← add_assoc, ← add_smul]
    congr
    exact mul_left_cancel₀ (by norm_num) tsirelson_inequality_aux
  have pos : 0 ≤ (√2)⁻¹ • (P ^ 2 + Q ^ 2) := by
    have P_sa : star P = P := by
      simp only [P, star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa,
        T.B₁_sa]
    have Q_sa : star Q = Q := by
      simp only [Q, star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa,
        T.B₁_sa]
    have P2_nonneg : 0 ≤ P ^ 2 := by simpa only [P_sa, sq] using star_mul_self_nonneg P
    have Q2_nonneg : 0 ≤ Q ^ 2 := by simpa only [Q_sa, sq] using star_mul_self_nonneg Q
    exact smul_nonneg (by positivity) (add_nonneg P2_nonneg Q2_nonneg)
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add, w, Nat.cast_zero] using pos