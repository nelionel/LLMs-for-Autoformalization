import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot
namespace Nat
open Finset
def primeCounting' : ℕ → ℕ :=
  Nat.count Prime
def primeCounting (n : ℕ) : ℕ :=
  primeCounting' (n + 1)
@[inherit_doc] scoped[Nat.Prime] notation "π" => Nat.primeCounting
@[inherit_doc] scoped[Nat.Prime] notation "π'" => Nat.primeCounting'
open scoped Nat.Prime
@[simp]
theorem primeCounting_sub_one (n : ℕ) : π (n - 1) = π' n := by
  cases n <;> rfl
theorem monotone_primeCounting' : Monotone primeCounting' :=
  count_monotone Prime
theorem monotone_primeCounting : Monotone primeCounting :=
  monotone_primeCounting'.comp (monotone_id.add_const _)
@[simp]
theorem primeCounting'_nth_eq (n : ℕ) : π' (nth Prime n) = n :=
  count_nth_of_infinite infinite_setOf_prime _
theorem add_two_le_nth_prime (n : ℕ) : n + 2 ≤ nth Prime n :=
  nth_prime_zero_eq_two ▸ (nth_strictMono infinite_setOf_prime).add_le_nat n 0
theorem surjective_primeCounting' : Function.Surjective π' :=
  Nat.surjective_count_of_infinite_setOf infinite_setOf_prime
theorem surjective_primeCounting : Function.Surjective π := by
  suffices Function.Surjective (π ∘ fun n => n - 1) from this.of_comp
  convert surjective_primeCounting'
  ext
  exact primeCounting_sub_one _
open Filter
theorem tendsto_primeCounting' : Tendsto π' atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone' monotone_primeCounting'
  simp [Set.range_eq_univ.mpr surjective_primeCounting']
theorem tensto_primeCounting : Tendsto π atTop atTop :=
  (tendsto_add_atTop_iff_nat 1).mpr tendsto_primeCounting'
@[simp]
theorem prime_nth_prime (n : ℕ) : Prime (nth Prime n) :=
  nth_mem_of_infinite infinite_setOf_prime _
@[simp]
lemma primeCounting'_eq_zero_iff {n : ℕ} : n.primeCounting' = 0 ↔ n ≤ 2 := by
  rw [primeCounting', Nat.count_eq_zero ⟨_, Nat.prime_two⟩, Nat.nth_prime_zero_eq_two]
@[simp]
lemma primeCounting_eq_zero_iff {n : ℕ} : n.primeCounting = 0 ↔ n ≤ 1 := by
  simp [primeCounting]
@[simp]
lemma primeCounting_zero : primeCounting 0 = 0 :=
  primeCounting_eq_zero_iff.mpr zero_le_one
@[simp]
lemma primeCounting_one : primeCounting 1 = 0 :=
  primeCounting_eq_zero_iff.mpr le_rfl
theorem primesBelow_card_eq_primeCounting' (n : ℕ) : #n.primesBelow = primeCounting' n := by
  simp only [primesBelow, primeCounting']
  exact (count_eq_card_filter_range Prime n).symm
theorem primeCounting'_add_le {a k : ℕ} (h0 : 0 < a) (h1 : a < k) (n : ℕ) :
    π' (k + n) ≤ π' k + Nat.totient a * (n / a + 1) :=
  calc
    π' (k + n) ≤ #{p ∈ range k | p.Prime} + #{p ∈ Ico k (k + n) | p.Prime} := by
      rw [primeCounting', count_eq_card_filter_range, range_eq_Ico, ←
        Ico_union_Ico_eq_Ico (zero_le k) le_self_add, filter_union]
      apply card_union_le
    _ ≤ π' k + #{p ∈ Ico k (k + n) | p.Prime} := by
      rw [primeCounting', count_eq_card_filter_range]
    _ ≤ π' k + #{b ∈ Ico k (k + n) | a.Coprime b} := by
      refine add_le_add_left (card_le_card ?_) k.primeCounting'
      simp only [subset_iff, and_imp, mem_filter, mem_Ico]
      intro p succ_k_le_p p_lt_n p_prime
      constructor
      · exact ⟨succ_k_le_p, p_lt_n⟩
      · rw [coprime_comm]
        exact coprime_of_lt_prime h0 (gt_of_ge_of_gt succ_k_le_p h1) p_prime
    _ ≤ π' k + totient a * (n / a + 1) := by
      rw [add_le_add_iff_left]
      exact Ico_filter_coprime_le k n h0
end Nat