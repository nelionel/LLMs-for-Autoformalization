import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Multiset.Fintype
import Mathlib.FieldTheory.ChevalleyWarning
open Finset MvPolynomial
variable {ι : Type*}
section prime
variable {p : ℕ} [Fact p.Prime] {s : Finset ι}
set_option linter.unusedVariables false in
private noncomputable def f₁ (s : Finset ι) (a : ι → ZMod p) : MvPolynomial s (ZMod p) :=
  ∑ i, X i ^ (p - 1)
private noncomputable def f₂ (s : Finset ι) (a : ι → ZMod p) : MvPolynomial s (ZMod p) :=
  ∑ i : s, a i • X i ^ (p - 1)
private lemma totalDegree_f₁_add_totalDegree_f₂ {a : ι → ZMod p} :
    (f₁ s a).totalDegree + (f₂ s a).totalDegree < 2 * p - 1 := by
  calc
    _ ≤ (p - 1) + (p - 1) := by
      gcongr <;> apply totalDegree_finsetSum_le <;> rintro i _
      · exact (totalDegree_X_pow ..).le
      · exact (totalDegree_smul_le ..).trans (totalDegree_X_pow ..).le
    _ < 2 * p - 1 := by have := (Fact.out : p.Prime).two_le; omega
private theorem ZMod.erdos_ginzburg_ziv_prime (a : ι → ZMod p) (hs : #s = 2 * p - 1) :
    ∃ t ⊆ s, #t = p ∧ ∑ i ∈ t, a i = 0 := by
  haveI : NeZero p := inferInstance
  classical
  set N := Fintype.card {x // eval x (f₁ s a) = 0 ∧ eval x (f₂ s a) = 0}
  let zero_sol : {x // eval x (f₁ s a) = 0 ∧ eval x (f₂ s a) = 0} :=
    ⟨0, by simp [f₁, f₂, map_sum, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]⟩
  have hN₀ : 0 < N := @Fintype.card_pos _ _ ⟨zero_sol⟩
  have hs' : 2 * p - 1 = Fintype.card s := by simp [hs]
  have hpN : p ∣ N := char_dvd_card_solutions_of_add_lt p
    (totalDegree_f₁_add_totalDegree_f₂.trans_eq hs')
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card ((Fact.out : p.Prime).one_lt.trans_le <|
    Nat.le_of_dvd hN₀ hpN) zero_sol
  refine ⟨({a | x.1 a ≠ 0} : Finset _).map ⟨(↑), Subtype.val_injective⟩, ?_, ?_, ?_⟩
  · simp +contextual [subset_iff]
  · rw [card_map]
    refine Nat.eq_of_dvd_of_lt_two_mul (Finset.card_pos.2 ?_).ne' ?_ <|
      (Finset.card_filter_le _ _).trans_lt ?_
    · rw [← Subtype.coe_ne_coe, Function.ne_iff] at hx
      exact hx.imp (fun a ha ↦ mem_filter.2 ⟨Finset.mem_attach _ _, ha⟩)
    · rw [← CharP.cast_eq_zero_iff (ZMod p), ← Finset.sum_boole]
      simpa only [f₁, map_sum, ZMod.pow_card_sub_one, map_pow, eval_X] using x.2.1
    · rw [univ_eq_attach, card_attach, hs]
      exact tsub_lt_self (mul_pos zero_lt_two (Fact.out : p.Prime).pos) zero_lt_one
  · simpa [f₂, ZMod.pow_card_sub_one, Finset.sum_filter] using x.2.2
private theorem Int.erdos_ginzburg_ziv_prime (a : ι → ℤ) (hs : #s = 2 * p - 1) :
    ∃ t ⊆ s, #t = p ∧ ↑p ∣ ∑ i ∈ t, a i := by
  simpa [← Int.cast_sum, ZMod.intCast_zmod_eq_zero_iff_dvd]
    using ZMod.erdos_ginzburg_ziv_prime (Int.cast ∘ a) hs
end prime
section composite
variable {n : ℕ} {s : Finset ι}
theorem Int.erdos_ginzburg_ziv (a : ι → ℤ) (hs : 2 * n - 1 ≤ #s) :
    ∃ t ⊆ s, #t = n ∧ ↑n ∣ ∑ i ∈ t, a i := by
  classical
  induction n using Nat.prime_composite_induction generalizing ι with
  | zero => exact ⟨∅, by simp⟩
  | one => simpa using exists_subset_card_eq hs
  | prime p hp =>
    haveI := Fact.mk hp
    obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hs
    obtain ⟨u, hut, hu⟩ := Int.erdos_ginzburg_ziv_prime a ht
    exact ⟨u, hut.trans hts, hu⟩
  | composite m hm ihm n hn ihn =>
    suffices ∀ k ≤ 2 * m - 1, ∃ 𝒜 : Finset (Finset ι), #𝒜 = k ∧
      (𝒜 : Set (Finset ι)).Pairwise _root_.Disjoint ∧
        ∀ ⦃t⦄, t ∈ 𝒜 → t ⊆ s ∧ #t = n ∧ ↑n ∣ ∑ i ∈ t, a i by
      obtain ⟨𝒜, h𝒜card, h𝒜disj, h𝒜⟩ := this _ le_rfl
      obtain ⟨ℬ, hℬ𝒜, hℬcard, hℬ⟩ := ihm (fun t ↦ (∑ i ∈ t, a i) / n) h𝒜card.ge
      refine ⟨ℬ.biUnion fun x ↦ x, biUnion_subset.2 fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).1, ?_, ?_⟩
      · rw [card_biUnion (h𝒜disj.mono hℬ𝒜), sum_const_nat fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).2.1, hℬcard]
      rwa [sum_biUnion, natCast_mul, mul_comm, ← Int.dvd_div_iff_mul_dvd, Int.sum_div]
      · exact fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).2.2
      · exact dvd_sum fun t ht ↦ (h𝒜 <| hℬ𝒜 ht).2.2
      · exact h𝒜disj.mono hℬ𝒜
    rintro k hk
    induction' k with k ih
    · exact ⟨∅, by simp⟩
    obtain ⟨𝒜, h𝒜card, h𝒜disj, h𝒜⟩ := ih (Nat.le_of_succ_le hk)
    have : 2 * n - 1 ≤ #(s \ 𝒜.biUnion id) := by
      calc
        _ ≤ (2 * m - k) * n - 1 := by gcongr; omega
        _ = (2 * (m * n) - 1) - ∑ t ∈ 𝒜, #t := by
          rw [tsub_mul, mul_assoc, tsub_right_comm, sum_const_nat fun t ht ↦ (h𝒜 ht).2.1, h𝒜card]
        _ ≤ #s - #(𝒜.biUnion id) := by gcongr; exact card_biUnion_le
        _ ≤ #(s \ 𝒜.biUnion id) := le_card_sdiff ..
    obtain ⟨t₀, ht₀, ht₀card, ht₀sum⟩ := ihn a this
    have : t₀ ∉ 𝒜 := by
      rintro h
      obtain rfl : n = 0 := by
        simpa [← card_eq_zero, ht₀card] using sdiff_disjoint.mono ht₀ <| subset_biUnion_of_mem id h
      omega
    refine ⟨𝒜.cons t₀ this, by rw [card_cons, h𝒜card], ?_, ?_⟩
    · simp only [cons_eq_insert, coe_insert, Set.pairwise_insert_of_symmetric symmetric_disjoint,
        mem_coe, ne_eq]
      exact ⟨h𝒜disj, fun t ht _ ↦ sdiff_disjoint.mono ht₀ <| subset_biUnion_of_mem id ht⟩
    · simp only [cons_eq_insert, mem_insert, forall_eq_or_imp, and_assoc]
      exact ⟨ht₀.trans sdiff_subset, ht₀card, ht₀sum, h𝒜⟩
theorem ZMod.erdos_ginzburg_ziv (a : ι → ZMod n) (hs : 2 * n - 1 ≤ #s) :
    ∃ t ⊆ s, #t = n ∧ ∑ i ∈ t, a i = 0 := by
  simpa [← ZMod.intCast_zmod_eq_zero_iff_dvd] using Int.erdos_ginzburg_ziv (ZMod.cast ∘ a) hs
theorem Int.erdos_ginzburg_ziv_multiset (s : Multiset ℤ) (hs : 2 * n - 1 ≤ Multiset.card s) :
    ∃ t ≤ s, Multiset.card t = n ∧ ↑n ∣ t.sum := by
  obtain ⟨t, hts, ht⟩ := Int.erdos_ginzburg_ziv (s := s.toEnumFinset) Prod.fst (by simpa using hs)
  exact ⟨t.1.map Prod.fst, Multiset.map_fst_le_of_subset_toEnumFinset hts, by simpa using ht⟩
theorem ZMod.erdos_ginzburg_ziv_multiset (s : Multiset (ZMod n))
    (hs : 2 * n - 1 ≤ Multiset.card s) : ∃ t ≤ s, Multiset.card t = n ∧ t.sum = 0 := by
  obtain ⟨t, hts, ht⟩ := ZMod.erdos_ginzburg_ziv (s := s.toEnumFinset) Prod.fst (by simpa using hs)
  exact ⟨t.1.map Prod.fst, Multiset.map_fst_le_of_subset_toEnumFinset hts, by simpa using ht⟩
end composite