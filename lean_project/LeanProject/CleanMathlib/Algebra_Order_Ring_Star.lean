import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Star.Basic
namespace StarOrderedRing
example {R : Type*} [OrderedSemiring R] [StarRing R] [StarOrderedRing R] {x y : R} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : x * y = y * x := by
  rw [← IsSelfAdjoint.of_nonneg (mul_nonneg hy hx), star_mul, IsSelfAdjoint.of_nonneg hx,
    IsSelfAdjoint.of_nonneg hy]
private lemma mul_le_mul_of_nonneg_left {R : Type*} [CommSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {a b c : R} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [StarOrderedRing.nonneg_iff] at hc
  induction hc using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨x, rfl⟩ := h
    simp_rw [mul_assoc, mul_comm x, ← mul_assoc]
    exact conjugate_le_conjugate hab x
  | one => simp
  | mul x hx y hy =>
    simp only [← nonneg_iff, add_mul] at hx hy ⊢
    apply add_le_add <;> aesop
abbrev toOrderedCommSemiring (R : Type*) [CommSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] : OrderedCommSemiring R where
  add_le_add_left _ _ := add_le_add_left
  zero_le_one := zero_le_one
  mul_comm := mul_comm
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right a b c := by simpa only [mul_comm _ c] using mul_le_mul_of_nonneg_left
abbrev toOrderedCommRing (R : Type*) [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] : OrderedCommRing R where
  add_le_add_left _ _ := add_le_add_left
  zero_le_one := zero_le_one
  mul_comm := mul_comm
  mul_nonneg _ _ := let _ := toOrderedCommSemiring R; mul_nonneg
end StarOrderedRing