import Mathlib.Data.List.Chain
universe u
open Nat
namespace List
variable {α : Type u}
theorem getElem_range'_1 {n m} (i) (H : i < (range' n m).length) :
    (range' n m)[i] = n + i := by simp
theorem chain'_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain' r (range n.succ) ↔ ∀ m < n, r m m.succ := by
  rw [range_succ]
  induction' n with n hn
  · simp
  · rw [range_succ]
    simp only [append_assoc, singleton_append, chain'_append_cons_cons, chain'_singleton, and_true]
    rw [hn, forall_lt_succ]
theorem chain_range_succ (r : ℕ → ℕ → Prop) (n a : ℕ) :
    Chain r a (range n.succ) ↔ r a 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ_eq_map, chain_cons, and_congr_right_iff, ← chain'_range_succ, range_succ_eq_map]
  exact fun _ => Iff.rfl
@[deprecated (since := "2024-08-19")] alias nthLe_range' := get_range'
@[deprecated (since := "2024-08-19")] alias nthLe_range'_1 := getElem_range'_1
@[deprecated (since := "2024-08-19")] alias nthLe_range := get_range
section Ranges
def ranges : List ℕ → List (List ℕ)
  | [] => nil
  | a::l => range a::(ranges l).map (map (a + ·))
theorem ranges_disjoint (l : List ℕ) :
    Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rintro ⟨v, _, rfl⟩
      rw [mem_range] at hu
      omega
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel
theorem ranges_length (l : List ℕ) :
    l.ranges.map length = l := by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => 
    simp only [map, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr_left
    intro s _
    simp only [Function.comp_apply, length_map]
set_option linter.deprecated false in
@[deprecated "Use `List.ranges_flatten`." (since := "2024-10-17")]
lemma ranges_flatten' : ∀ l : List ℕ, l.ranges.flatten = range (Nat.sum l)
  | [] => rfl
  | a :: l => by simp only [Nat.sum_cons, flatten, ← map_flatten, ranges_flatten', range_add]
@[deprecated (since := "2024-10-15")] alias ranges_join' := ranges_flatten'
set_option linter.deprecated false in
@[deprecated "Use `List.mem_mem_ranges_iff_lt_sum`." (since := "2024-11-18")]
lemma mem_mem_ranges_iff_lt_natSum (l : List ℕ) {n : ℕ} :
    (∃ s ∈ l.ranges, n ∈ s) ↔ n < Nat.sum l := by
  rw [← mem_range, ← ranges_flatten', mem_flatten]
end Ranges
end List