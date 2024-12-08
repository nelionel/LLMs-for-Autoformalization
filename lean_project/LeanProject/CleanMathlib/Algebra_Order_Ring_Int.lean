import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Set.Basic
assert_not_exists Set.Subsingleton
open Function Nat
namespace Int
instance instLinearOrderedCommRing : LinearOrderedCommRing ℤ where
  __ := instCommRing
  __ := instLinearOrder
  add_le_add_left := @Int.add_le_add_left
  mul_pos := @Int.mul_pos
  zero_le_one := le_of_lt Int.zero_lt_one
instance instOrderedCommRing : OrderedCommRing ℤ := StrictOrderedCommRing.toOrderedCommRing'
instance instOrderedRing : OrderedRing ℤ := StrictOrderedRing.toOrderedRing'
lemma isCompl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by
  simp [← not_even_iff_odd, ← Set.compl_setOf, isCompl_compl]
lemma _root_.Nat.cast_natAbs {α : Type*} [AddGroupWithOne α] (n : ℤ) : (n.natAbs : α) = |n| := by
  rw [← natCast_natAbs, Int.cast_natCast]
lemma cast_mul_eq_zsmul_cast {α : Type*} [AddCommGroupWithOne α] :
    ∀ m n : ℤ, ↑(m * n) = m • (n : α) :=
  fun m ↦ Int.induction_on m (by simp) (fun _ ih ↦ by simp [add_mul, add_zsmul, ih]) fun _ ih ↦ by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]
lemma two_le_iff_pos_of_even {m : ℤ} (even : Even m) : 2 ≤ m ↔ 0 < m :=
  le_iff_pos_of_dvd (by decide) even.two_dvd
lemma add_two_le_iff_lt_of_even_sub {m n : ℤ} (even : Even (n - m)) : m + 2 ≤ n ↔ m < n := by
  rw [add_comm]; exact le_add_iff_lt_of_dvd_sub (by decide) even.two_dvd
end Int