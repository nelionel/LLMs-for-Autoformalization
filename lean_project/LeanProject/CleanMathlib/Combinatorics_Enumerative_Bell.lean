import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Mul
open Multiset Nat
namespace Multiset
def bell (m : Multiset ℕ) : ℕ :=
  Nat.multinomial m.toFinset (fun k ↦ k * m.count k) *
    ∏ k ∈ m.toFinset.erase 0, ∏ j ∈ .range (m.count k), (j * k + k - 1).choose (k - 1)
@[simp]
theorem bell_zero : bell 0 = 1 := rfl
private theorem bell_mul_eq_lemma {x : ℕ} (hx : x ≠ 0) :
    ∀ c, x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!
  | 0 => by simp
  | c + 1 => calc
      x ! ^ (c + 1) * (c + 1)! * ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1)
        = x ! * (c + 1) * x ! ^ c * c ! *
            ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1) := by
        rw [factorial_succ, pow_succ]; ring
      _ = (x ! ^ c * c ! * ∏ j in Finset.range c, (j * x + x - 1).choose (x - 1)) *
            (c * x + x - 1).choose (x - 1) * x ! * (c + 1)  := by
        rw [Finset.prod_range_succ]; ring
      _ = (c + 1) * (c * x + x - 1).choose (x - 1) * (x * c)! * x ! := by
        rw [bell_mul_eq_lemma hx]; ring
      _ = (x * (c + 1))! := by
        rw [← Nat.choose_mul_add hx, mul_comm c x, Nat.add_choose_mul_factorial_mul_factorial]
        ring_nf
theorem bell_mul_eq (m : Multiset ℕ) :
    m.bell * (m.map (fun j ↦ j !)).prod * ∏ j ∈ (m.toFinset.erase 0), (m.count j)!
      = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i ∈ m.toFinset, (i * count i m)!) (by positivity)]
  simp only [← mul_assoc]
  rw [Nat.multinomial_spec]
  simp only [mul_assoc]
  rw [mul_comm]
  apply congr_arg₂
  · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
    suffices this : _ by
      by_cases hm : 0 ∈ m.toFinset
      · rw [← Finset.prod_erase_mul _ _ hm]
        rw [← Finset.prod_erase_mul _ _ hm]
        simp only [factorial_zero, one_pow, mul_one, zero_mul]
        exact this
      · nth_rewrite 1 [← Finset.erase_eq_of_not_mem hm]
        nth_rewrite 3 [← Finset.erase_eq_of_not_mem hm]
        exact this
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x hx
    rw [← mul_assoc, bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · apply congr_arg
    rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]
theorem bell_eq (m : Multiset ℕ) :
    m.bell = m.sum ! / ((m.map (fun j ↦ j !)).prod *
      ∏ j ∈ (m.toFinset.erase 0), (m.count j)!) := by
  rw [← Nat.mul_left_inj, Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    apply Nat.mul_pos
    · simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.multiset_prod_pos, mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun _ _ ↦ Nat.factorial_pos _
    · apply Finset.prod_pos
      exact fun _ _ ↦ Nat.factorial_pos _
end Multiset
namespace Nat
def uniformBell (m n : ℕ) : ℕ := bell (replicate m n)
theorem uniformBell_eq (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), Nat.choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp  [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]
theorem uniformBell_zero_left (n : ℕ) : uniformBell 0 n = 1 := by
  simp [uniformBell_eq]
theorem uniformBell_zero_right (m : ℕ) : uniformBell m 0 = 1 := by
  simp [uniformBell_eq]
theorem uniformBell_succ_left (m n : ℕ) :
    uniformBell (m+1) n = choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]
theorem uniformBell_one_left (n : ℕ) : uniformBell 1 n = 1 := by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]
theorem uniformBell_one_right (m : ℕ) : uniformBell m 1 = 1 := by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]
theorem uniformBell_mul_eq (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n * n ! ^ m * m ! = (m * n)! := by
  convert bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [toFinset_replicate]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset ℕ).erase 0 = ∅ from rfl,  Finset.prod_empty]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp
theorem uniformBell_eq_div (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n = (m * n) ! / (n ! ^ m * m !) := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos (Nat.factorial_pos n)) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]
end Nat