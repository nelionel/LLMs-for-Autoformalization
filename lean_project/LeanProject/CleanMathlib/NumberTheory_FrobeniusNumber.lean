import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
open Nat
def FrobeniusNumber (n : ℕ) (s : Set ℕ) : Prop :=
  IsGreatest { k | k ∉ AddSubmonoid.closure s } n
variable {m n : ℕ}
theorem frobeniusNumber_pair (cop : Coprime m n) (hm : 1 < m) (hn : 1 < n) :
    FrobeniusNumber (m * n - m - n) {m, n} := by
  simp_rw [FrobeniusNumber, AddSubmonoid.mem_closure_pair]
  have hmn : m + n ≤ m * n := add_le_mul hm hn
  constructor
  · push_neg
    intro a b h
    apply cop.mul_add_mul_ne_mul (add_one_ne_zero a) (add_one_ne_zero b)
    simp only [Nat.sub_sub, smul_eq_mul] at h
    zify [hmn] at h ⊢
    rw [← sub_eq_zero] at h ⊢
    rw [← h]
    ring
  · intro k hk
    dsimp at hk
    contrapose! hk
    let x := chineseRemainder cop 0 k
    have hx : x.val < m * n := chineseRemainder_lt_mul cop 0 k (ne_bot_of_gt hm) (ne_bot_of_gt hn)
    suffices key : x.1 ≤ k by
      obtain ⟨a, ha⟩ := modEq_zero_iff_dvd.mp x.2.1
      obtain ⟨b, hb⟩ := (modEq_iff_dvd' key).mp x.2.2
      exact ⟨a, b, by rw [mul_comm, ← ha, mul_comm, ← hb, Nat.add_sub_of_le key]⟩
    refine ModEq.le_of_lt_add x.2.2 (lt_of_le_of_lt ?_ (add_lt_add_right hk n))
    rw [Nat.sub_add_cancel (le_tsub_of_add_le_left hmn)]
    exact
      ModEq.le_of_lt_add
        (x.2.1.trans (modEq_zero_iff_dvd.mpr (Nat.dvd_sub' (dvd_mul_right m n) dvd_rfl)).symm)
        (lt_of_lt_of_le hx le_tsub_add)