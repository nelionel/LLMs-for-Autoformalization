import Mathlib.Analysis.Matrix
import Mathlib.Data.Pi.Interval
import Mathlib.Tactic.Rify
attribute [local instance] Matrix.seminormedAddCommGroup
open Matrix Finset
namespace Int.Matrix
variable {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)
local notation3 "m" => Fintype.card α
local notation3 "n" => Fintype.card β
local notation3 "e" => m / ((n : ℝ) - m) 
local notation3 "B" => Nat.floor (((n : ℝ) * max 1 ‖A‖) ^ e)
local notation3 "B'" => fun _ : β => (B : ℤ)
local notation3 "T" =>  Finset.Icc 0 B'
local notation3 "P" => fun i : α => ∑ j : β, B * posPart (A i j)
local notation3 "N" => fun i : α => ∑ j : β, B * (- negPart (A i j))
local notation3 "S" => Finset.Icc N P
section preparation
private lemma image_T_subset_S [DecidableEq α] [DecidableEq β] (v) (hv : v ∈ T) : A *ᵥ v ∈ S := by
  rw [mem_Icc] at hv ⊢
  have mulVec_def : A.mulVec v =
      fun i ↦ Finset.sum univ fun j : β ↦ A i j * v j := rfl
  rw [mulVec_def]
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  all_goals
    simp only [mul_neg]
    gcongr ∑ _ : α, ?_ with j _ 
    rw [← mul_comm (v j)] 
    rcases le_total 0 (A i j) with hsign | hsign
  · rw [negPart_eq_zero.2 hsign]
    exact mul_nonneg (hv.1 j) hsign
  · rw [negPart_eq_neg.2 hsign]
    simp only [mul_neg, neg_neg]
    exact mul_le_mul_of_nonpos_right (hv.2 j) hsign
  · rw [posPart_eq_self.2 hsign]
    exact mul_le_mul_of_nonneg_right (hv.2 j) hsign
  · rw [posPart_eq_zero.2 hsign]
    exact mul_nonpos_of_nonneg_of_nonpos (hv.1 j) hsign
private lemma card_T_eq [DecidableEq β] : #T = (B + 1) ^ n := by
  rw [Pi.card_Icc 0 B']
  simp only [Pi.zero_apply, card_Icc, sub_zero, toNat_ofNat_add_one, prod_const, card_univ,
    add_pos_iff, zero_lt_one, or_true]
private lemma N_le_P_add_one (i : α) : N i ≤ P i + 1 := by
  calc N i
  _ ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    simp only [mul_neg, Left.neg_nonpos_iff]
    exact mul_nonneg (Nat.cast_nonneg B) (negPart_nonneg (A i j))
  _ ≤ P i + 1 := by
    apply le_trans (Finset.sum_nonneg _) (Int.le_add_one (le_refl P i))
    intro j _
    exact mul_nonneg (Nat.cast_nonneg B) (posPart_nonneg (A i j))
private lemma card_S_eq [DecidableEq α] : #(Finset.Icc N P) = ∏ i : α, (P i - N i + 1) := by
  rw [Pi.card_Icc N P, Nat.cast_prod]
  congr
  ext i
  rw [Int.card_Icc_of_le (N i) (P i) (N_le_P_add_one A i)]
  exact add_sub_right_comm (P i) 1 (N i)
lemma one_le_norm_A_of_ne_zero (hA : A ≠ 0) : 1 ≤ ‖A‖ := by
  by_contra! h
  apply hA
  ext i j
  simp only [zero_apply]
  rw [norm_lt_iff Real.zero_lt_one] at h
  specialize h i j
  rw [Int.norm_eq_abs] at h
  norm_cast at h
  exact Int.abs_lt_one_iff.1 h
open Real Nat
private lemma card_S_lt_card_T [DecidableEq α] [DecidableEq β]
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    #S < #T := by
  zify 
  rw [card_T_eq A, card_S_eq]
  rify 
  calc
  ∏ x : α, (∑ x_1 : β, ↑B * ↑(A x x_1)⁺ - ∑ x_1 : β, ↑B * -↑(A x x_1)⁻ + 1)
    ≤ ∏ x : α, (n * max 1 ‖A‖ * B + 1) := by
      refine Finset.prod_le_prod (fun i _ ↦ ?_) (fun i _ ↦ ?_)
      · have h := N_le_P_add_one A i
        rify at h
        linarith only [h]
      · simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, add_le_add_iff_right]
        have h1 : n * max 1 ‖A‖ * B = ∑ _ : β, max 1 ‖A‖ * B := by
          simp only [sum_const, card_univ, nsmul_eq_mul]
          ring
        simp_rw [h1, ← Finset.sum_add_distrib, ← mul_add, mul_comm (max 1 ‖A‖), ← Int.cast_add]
        gcongr with j _
        rw [posPart_add_negPart (A i j), Int.cast_abs]
        exact le_trans (norm_entry_le_entrywise_sup_norm A) (le_max_right ..)
  _  = (n * max 1 ‖A‖ * B + 1) ^ m := by simp only [prod_const, card_univ]
  _  ≤ (n * max 1 ‖A‖) ^ m * (B + 1) ^ m := by
        rw [← mul_pow, mul_add, mul_one]
        gcongr
        have H : 1 ≤ (n : ℝ) := mod_cast (hm.trans hn)
        exact one_le_mul_of_one_le_of_one_le H <| le_max_left ..
  _ = ((n * max 1 ‖A‖) ^ (m / ((n : ℝ) - m))) ^ ((n : ℝ) - m)  * (B + 1) ^ m := by
        congr 1
        rw [← rpow_mul (mul_nonneg (Nat.cast_nonneg' n) (le_trans zero_le_one (le_max_left ..))),
          ← Real.rpow_natCast, div_mul_cancel₀]
        exact sub_ne_zero_of_ne (mod_cast hn.ne')
  _ < (B + 1) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        gcongr
        · exact sub_pos.mpr (mod_cast hn)
        · exact Nat.lt_floor_add_one ((n * max 1 ‖A‖) ^ e)
  _ = (B + 1) ^ n := by
        rw [← rpow_natCast, ← rpow_add (Nat.cast_add_one_pos B), ← rpow_natCast, sub_add_cancel]
end preparation
theorem exists_ne_zero_int_vec_norm_le
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) : ∃ t : β → ℤ, t ≠ 0 ∧
    A *ᵥ t = 0 ∧ ‖t‖ ≤ (n * max 1 ‖A‖) ^ ((m : ℝ) / (n - m)) := by
  classical
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (card_S_lt_card_T A hn hm) (image_T_subset_S A)
    with ⟨x, hxT, y, hyT, hneq, hfeq⟩
  refine ⟨x - y, sub_ne_zero.mpr hneq, by simp only [mulVec_sub, sub_eq_zero, hfeq], ?_⟩
  have n_mul_norm_A_pow_e_nonneg : 0 ≤ (n * max 1 ‖A‖) ^ e := by positivity
  rw [← norm_col (ι := Unit), norm_le_iff n_mul_norm_A_pow_e_nonneg]
  intro i j
  simp only [col_apply, Pi.sub_apply]
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  refine le_trans ?_ (Nat.floor_le n_mul_norm_A_pow_e_nonneg)
  norm_cast
  rw [abs_le]
  rw [Finset.mem_Icc] at hxT hyT
  constructor
  · simp only [neg_le_sub_iff_le_add]
    apply le_trans (hyT.2 i)
    norm_cast
    simp only [le_add_iff_nonneg_left]
    exact hxT.1 i
  · simp only [tsub_le_iff_right]
    apply le_trans (hxT.2 i)
    norm_cast
    simp only [le_add_iff_nonneg_right]
    exact hyT.1 i
theorem exists_ne_zero_int_vec_norm_le'
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) (hA : A ≠ 0) :
    ∃ t : β → ℤ, t ≠ 0 ∧
    A *ᵥ t = 0 ∧ ‖t‖ ≤ (n * ‖A‖) ^ ((m : ℝ) / (n - m)) := by
  have := exists_ne_zero_int_vec_norm_le A hn hm
  rwa [max_eq_right] at this
  exact Int.Matrix.one_le_norm_A_of_ne_zero _ hA
end Int.Matrix