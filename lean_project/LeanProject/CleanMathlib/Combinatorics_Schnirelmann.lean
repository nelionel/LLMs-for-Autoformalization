import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Nat
open Finset
noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  ⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n
section
variable {A : Set ℕ} [DecidablePred (· ∈ A)]
lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A :=
  Real.iInf_nonneg (fun _ => by positivity)
lemma schnirelmannDensity_le_div {n : ℕ} (hn : n ≠ 0) :
    schnirelmannDensity A ≤ #{a ∈ Ioc 0 n | a ∈ A} / n :=
  ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ (⟨n, hn.bot_lt⟩ : {n : ℕ // 0 < n})
lemma schnirelmannDensity_mul_le_card_filter {n : ℕ} :
    schnirelmannDensity A * n ≤ #{a ∈ Ioc 0 n | a ∈ A} := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff₀ (by positivity)).1 (schnirelmannDensity_le_div hn)
lemma schnirelmannDensity_le_of_le {x : ℝ} (n : ℕ) (hn : n ≠ 0)
    (hx : #{a ∈ Ioc 0 n | a ∈ A} / n ≤ x) : schnirelmannDensity A ≤ x :=
  (schnirelmannDensity_le_div hn).trans hx
lemma schnirelmannDensity_le_one : schnirelmannDensity A ≤ 1 :=
  schnirelmannDensity_le_of_le 1 one_ne_zero <|
    by rw [Nat.cast_one, div_one, Nat.cast_le_one]; exact card_filter_le _ _
lemma schnirelmannDensity_le_of_not_mem {k : ℕ} (hk : k ∉ A) :
    schnirelmannDensity A ≤ 1 - (k⁻¹ : ℝ) := by
  rcases k.eq_zero_or_pos with rfl | hk'
  · simpa using schnirelmannDensity_le_one
  apply schnirelmannDensity_le_of_le k hk'.ne'
  rw [← one_div, one_sub_div (Nat.cast_pos.2 hk').ne']
  gcongr
  rw [← Nat.cast_pred hk', Nat.cast_le]
  suffices {a ∈ Ioc 0 k | a ∈ A} ⊆ Ioo 0 k from (card_le_card this).trans_eq (by simp)
  rw [← Ioo_insert_right hk', filter_insert, if_neg hk]
  exact filter_subset _ _
lemma schnirelmannDensity_eq_zero_of_one_not_mem (h : 1 ∉ A) : schnirelmannDensity A = 0 :=
  ((schnirelmannDensity_le_of_not_mem h).trans (by simp)).antisymm schnirelmannDensity_nonneg
lemma schnirelmannDensity_le_of_subset {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A ⊆ B) :
    schnirelmannDensity A ≤ schnirelmannDensity B :=
  ciInf_mono ⟨0, fun _ ⟨_, hx⟩ ↦ hx ▸ by positivity⟩ fun _ ↦ by
    gcongr; exact h
lemma schnirelmannDensity_eq_one_iff : schnirelmannDensity A = 1 ↔ {0}ᶜ ⊆ A := by
  rw [le_antisymm_iff, and_iff_right schnirelmannDensity_le_one]
  constructor
  · rw [← not_imp_not, not_le]
    simp only [Set.not_subset, forall_exists_index, true_and, and_imp, Set.mem_singleton_iff]
    intro x hx hx'
    apply (schnirelmannDensity_le_of_not_mem hx').trans_lt
    simpa only [one_div, sub_lt_self_iff, inv_pos, Nat.cast_pos, pos_iff_ne_zero] using hx
  · intro h
    refine le_ciInf fun ⟨n, hn⟩ => ?_
    rw [one_le_div (Nat.cast_pos.2 hn), Nat.cast_le, filter_true_of_mem, Nat.card_Ioc, Nat.sub_zero]
    rintro x hx
    exact h (mem_Ioc.1 hx).1.ne'
lemma schnirelmannDensity_eq_one_iff_of_zero_mem (hA : 0 ∈ A) :
    schnirelmannDensity A = 1 ↔ A = Set.univ := by
  rw [schnirelmannDensity_eq_one_iff]
  constructor
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact hA
    · exact h hx
  · rintro rfl
    exact Set.subset_univ {0}ᶜ
lemma le_schnirelmannDensity_iff {x : ℝ} :
    x ≤ schnirelmannDensity A ↔ ∀ n : ℕ, 0 < n → x ≤ #{a ∈ Ioc 0 n | a ∈ A} / n :=
  (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall
lemma schnirelmannDensity_lt_iff {x : ℝ} :
    schnirelmannDensity A < x ↔ ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x := by
  rw [← not_le, le_schnirelmannDensity_iff]; simp
lemma schnirelmannDensity_le_iff_forall {x : ℝ} :
    schnirelmannDensity A ≤ x ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x + ε := by
  rw [le_iff_forall_pos_lt_add]
  simp only [schnirelmannDensity_lt_iff]
lemma schnirelmannDensity_congr' {B : Set ℕ} [DecidablePred (· ∈ B)]
    (h : ∀ n > 0, n ∈ A ↔ n ∈ B) : schnirelmannDensity A = schnirelmannDensity B := by
  rw [schnirelmannDensity, schnirelmannDensity]; congr; ext ⟨n, hn⟩; congr 3; ext x; aesop
@[simp] lemma schnirelmannDensity_insert_zero [DecidablePred (· ∈ insert 0 A)] :
    schnirelmannDensity (insert 0 A) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)
lemma schnirelmannDensity_diff_singleton_zero [DecidablePred (· ∈ A \ {0})] :
    schnirelmannDensity (A \ {0}) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)
lemma schnirelmannDensity_congr {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A = B) :
    schnirelmannDensity A = schnirelmannDensity B :=
  schnirelmannDensity_congr' (by aesop)
lemma exists_of_schnirelmannDensity_eq_zero {ε : ℝ} (hε : 0 < ε) (hA : schnirelmannDensity A = 0) :
    ∃ n, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < ε := by
  by_contra! h
  rw [← le_schnirelmannDensity_iff] at h
  linarith
end
@[simp] lemma schnirelmannDensity_empty : schnirelmannDensity ∅ = 0 :=
  schnirelmannDensity_eq_zero_of_one_not_mem (by simp)
lemma schnirelmannDensity_finset (A : Finset ℕ) : schnirelmannDensity A = 0 := by
  refine le_antisymm ?_ schnirelmannDensity_nonneg
  simp only [schnirelmannDensity_le_iff_forall, zero_add]
  intro ε hε
  wlog hε₁ : ε ≤ 1 generalizing ε
  · obtain ⟨n, hn, hn'⟩ := this 1 zero_lt_one le_rfl
    exact ⟨n, hn, hn'.trans_le (le_of_not_le hε₁)⟩
  let n : ℕ := ⌊#A / ε⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  use n, hn
  rw [div_lt_iff₀ (Nat.cast_pos.2 hn), ← div_lt_iff₀' hε, Nat.cast_add_one]
  exact (Nat.lt_floor_add_one _).trans_le' <| by gcongr; simp [subset_iff]
lemma schnirelmannDensity_finite {A : Set ℕ} [DecidablePred (· ∈ A)] (hA : A.Finite) :
    schnirelmannDensity A = 0 := by simpa using schnirelmannDensity_finset hA.toFinset
@[simp] lemma schnirelmannDensity_univ : schnirelmannDensity Set.univ = 1 :=
  (schnirelmannDensity_eq_one_iff_of_zero_mem (by simp)).2 (by simp)
lemma schnirelmannDensity_setOf_even : schnirelmannDensity (setOf Even) = 0 :=
  schnirelmannDensity_eq_zero_of_one_not_mem <| by simp
lemma schnirelmannDensity_setOf_prime : schnirelmannDensity (setOf Nat.Prime) = 0 :=
  schnirelmannDensity_eq_zero_of_one_not_mem <| by simp [Nat.not_prime_one]
lemma schnirelmannDensity_setOf_mod_eq_one {m : ℕ} (hm : m ≠ 1) :
    schnirelmannDensity {n | n % m = 1} = (m⁻¹ : ℝ) := by
  rcases m.eq_zero_or_pos with rfl | hm'
  · simp only [Nat.cast_zero, inv_zero]
    refine schnirelmannDensity_finite ?_
    simp
  apply le_antisymm (schnirelmannDensity_le_of_le m hm'.ne' _) _
  · rw [← one_div, ← @Nat.cast_one ℝ]
    gcongr
    simp only [Set.mem_setOf_eq, card_le_one_iff_subset_singleton, subset_iff,
      mem_filter, mem_Ioc, mem_singleton, and_imp]
    use 1
    intro x _ hxm h
    rcases eq_or_lt_of_le hxm with rfl | hxm'
    · simp at h
    rwa [Nat.mod_eq_of_lt hxm'] at h
  rw [le_schnirelmannDensity_iff]
  intro n hn
  simp only [Set.mem_setOf_eq]
  have : (Icc 0 ((n - 1) / m)).image (· * m + 1) ⊆ {x ∈ Ioc 0 n | x % m = 1} := by
    simp only [subset_iff, mem_image, forall_exists_index, mem_filter, mem_Ioc, mem_Icc, and_imp]
    rintro _ y _ hy' rfl
    have hm : 2 ≤ m := hm.lt_of_le' hm'
    simp only [Nat.mul_add_mod', Nat.mod_eq_of_lt hm, add_pos_iff, or_true, and_true, true_and,
      ← Nat.le_sub_iff_add_le hn, zero_lt_one]
    exact Nat.mul_le_of_le_div _ _ _ hy'
  rw [le_div_iff₀ (Nat.cast_pos.2 hn), mul_comm, ← div_eq_mul_inv]
  apply (Nat.cast_le.2 (card_le_card this)).trans'
  rw [card_image_of_injective, Nat.card_Icc, Nat.sub_zero, div_le_iff₀ (Nat.cast_pos.2 hm'),
    ← Nat.cast_mul, Nat.cast_le, add_one_mul (α := ℕ)]
  · have := @Nat.lt_div_mul_add n.pred m hm'
    rwa [← Nat.succ_le, Nat.succ_pred hn.ne'] at this
  intro a b
  simp [hm'.ne']
lemma schnirelmannDensity_setOf_modeq_one {m : ℕ} :
    schnirelmannDensity {n | n ≡ 1 [MOD m]} = (m⁻¹ : ℝ) := by
  rcases eq_or_ne m 1 with rfl | hm
  · simp [Nat.modEq_one]
  rw [← schnirelmannDensity_setOf_mod_eq_one hm]
  apply schnirelmannDensity_congr
  ext n
  simp only [Set.mem_setOf_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hm]
lemma schnirelmannDensity_setOf_Odd : schnirelmannDensity (setOf Odd) = 2⁻¹ := by
  have h : setOf Odd = {n | n % 2 = 1} := Set.ext fun _ => Nat.odd_iff
  simp only [h]
  rw [schnirelmannDensity_setOf_mod_eq_one (by norm_num1), Nat.cast_two]