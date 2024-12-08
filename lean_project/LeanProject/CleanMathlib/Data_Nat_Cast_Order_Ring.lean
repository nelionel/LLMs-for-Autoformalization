import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Nat.Cast.Order.Basic
variable {α : Type*}
namespace Nat
section OrderedSemiring
variable [AddMonoidWithOne α] [PartialOrder α]
variable [AddLeftMono α] [ZeroLEOneClass α]
@[simp]
theorem cast_nonneg {α} [OrderedSemiring α] (n : ℕ) : 0 ≤ (n : α) :=
  cast_nonneg' n
@[simp]
theorem ofNat_nonneg {α} [OrderedSemiring α] (n : ℕ) [n.AtLeastTwo] :
    0 ≤ (no_index (OfNat.ofNat n : α)) :=
  ofNat_nonneg' n
@[simp, norm_cast]
theorem cast_min {α} [LinearOrderedSemiring α] (m n : ℕ) : (↑(min m n : ℕ) : α) = min (m : α) n :=
  (@mono_cast α _).map_min
@[simp, norm_cast]
theorem cast_max {α} [LinearOrderedSemiring α] (m n : ℕ) : (↑(max m n : ℕ) : α) = max (m : α) n :=
  (@mono_cast α _).map_max
section Nontrivial
variable [NeZero (1 : α)]
@[simp]
theorem cast_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} : (0 : α) < n ↔ 0 < n := cast_pos'
@[simp low]
theorem ofNat_pos' {n : ℕ} [n.AtLeastTwo] : 0 < (no_index (OfNat.ofNat n : α)) :=
  cast_pos'.mpr (NeZero.pos n)
@[simp]
theorem ofNat_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} [n.AtLeastTwo] :
    0 < (no_index (OfNat.ofNat n : α)) :=
  ofNat_pos'
end Nontrivial
end OrderedSemiring
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [AddLeftReflectLE α] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]
@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)
@[simp]
theorem abs_ofNat [LinearOrderedRing α] (n : ℕ) [n.AtLeastTwo] :
    |(no_index (OfNat.ofNat n : α))| = OfNat.ofNat n :=
  abs_cast n
lemma mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) :
    a * b ≤ a ^ b := by
  induction b generalizing a with
  | zero => simp
  | succ b hb =>
    rw [mul_add_one, pow_succ]
    rcases a with (_|_|a)
    · simp
    · simp at ha
    · rw [mul_add_one, mul_add_one, add_comm (_ * a), add_assoc _ (_ * a)]
      rcases b with (_|b)
      · simp [add_assoc, add_comm]
      refine add_le_add (hb (by simp)) ?_
      rw [pow_succ']
      refine (le_add_left ?_ ?_).trans' ?_
      exact le_mul_of_one_le_right' (one_le_pow _ _ (by simp))
lemma two_mul_sq_add_one_le_two_pow_two_mul (k : ℕ) : 2 * k ^ 2 + 1 ≤ 2 ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [add_pow_two, one_pow, mul_one, add_assoc, mul_add, add_right_comm]
    refine (add_le_add_right hk _).trans ?_
    rw [mul_add 2 k, pow_add, mul_one, pow_two, ← mul_assoc, mul_two, mul_two, add_assoc]
    gcongr
    rw [← two_mul, ← pow_succ']
    exact le_add_of_le_right (mul_le_pow (by simp) _)
end Nat