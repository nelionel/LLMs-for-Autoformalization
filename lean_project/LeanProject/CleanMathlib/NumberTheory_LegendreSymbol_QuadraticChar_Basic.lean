import Mathlib.Data.Fintype.Parity
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.FieldTheory.Finite.Basic
section Define
def quadraticCharFun (α : Type*) [MonoidWithZero α] [DecidableEq α]
    [DecidablePred (IsSquare : α → Prop)] (a : α) : ℤ :=
  if a = 0 then 0 else if IsSquare a then 1 else -1
end Define
section quadraticChar
open MulChar
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem quadraticCharFun_eq_zero_iff {a : F} : quadraticCharFun F a = 0 ↔ a = 0 := by
  simp only [quadraticCharFun]
  by_cases ha : a = 0
  · simp only [ha, if_true]
  · simp only [ha, if_false]
    split_ifs <;> simp only [neg_eq_zero, one_ne_zero, not_false_iff]
@[simp]
theorem quadraticCharFun_zero : quadraticCharFun F 0 = 0 := by
  simp only [quadraticCharFun, if_true]
@[simp]
theorem quadraticCharFun_one : quadraticCharFun F 1 = 1 := by
  simp only [quadraticCharFun, one_ne_zero, isSquare_one, if_true, if_false]
theorem quadraticCharFun_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = 1 := by
  simp only [quadraticCharFun, ha, if_false, ite_eq_left_iff]
  exact fun h ↦ (h (FiniteField.isSquare_of_char_two hF a)).elim
theorem quadraticCharFun_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 := by
  simp only [quadraticCharFun, ha, if_false]
  simp_rw [FiniteField.isSquare_iff hF ha]
theorem quadraticCharFun_mul (a b : F) :
    quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b := by
  by_cases ha : a = 0
  · rw [ha, zero_mul, quadraticCharFun_zero, zero_mul]
  by_cases hb : b = 0
  · rw [hb, mul_zero, quadraticCharFun_zero, mul_zero]
  have hab := mul_ne_zero ha hb
  by_cases hF : ringChar F = 2
  ·
    rw [quadraticCharFun_eq_one_of_char_two hF ha, quadraticCharFun_eq_one_of_char_two hF hb,
      quadraticCharFun_eq_one_of_char_two hF hab, mul_one]
  · 
    rw [quadraticCharFun_eq_pow_of_char_ne_two hF ha, quadraticCharFun_eq_pow_of_char_ne_two hF hb,
      quadraticCharFun_eq_pow_of_char_ne_two hF hab, mul_pow]
    cases' FiniteField.pow_dichotomy hF hb with hb' hb'
    · simp only [hb', mul_one, if_true]
    · have h := Ring.neg_one_ne_one_of_char_ne_two hF
      simp only [hb', mul_neg, mul_one, h, if_false]
      cases' FiniteField.pow_dichotomy hF ha with ha' ha' <;>
        simp only [ha', h, neg_neg, if_true, if_false]
variable (F)
@[simps]
def quadraticChar : MulChar F ℤ where
  toFun := quadraticCharFun F
  map_one' := quadraticCharFun_one
  map_mul' := quadraticCharFun_mul
  map_nonunit' a ha := by rw [of_not_not (mt Ne.isUnit ha)]; exact quadraticCharFun_zero
variable {F}
theorem quadraticChar_eq_zero_iff {a : F} : quadraticChar F a = 0 ↔ a = 0 :=
  quadraticCharFun_eq_zero_iff
theorem quadraticChar_zero : quadraticChar F 0 = 0 := by
  simp only [quadraticChar_apply, quadraticCharFun_zero]
theorem quadraticChar_one_iff_isSquare {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ↔ IsSquare a := by
  simp only [quadraticChar_apply, quadraticCharFun, ha, if_false, ite_eq_left_iff,
    (by omega : (-1 : ℤ) ≠ 1), imp_false, not_not, reduceCtorEq]
theorem quadraticChar_sq_one' {a : F} (ha : a ≠ 0) : quadraticChar F (a ^ 2) = 1 := by
  simp only [quadraticChar_apply, quadraticCharFun, sq_eq_zero_iff, ha, IsSquare_sq, if_true,
    if_false]
theorem quadraticChar_sq_one {a : F} (ha : a ≠ 0) : quadraticChar F a ^ 2 = 1 := by
  rwa [pow_two, ← map_mul, ← pow_two, quadraticChar_sq_one']
theorem quadraticChar_dichotomy {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ∨ quadraticChar F a = -1 :=
  sq_eq_one_iff.1 <| quadraticChar_sq_one ha
theorem quadraticChar_eq_neg_one_iff_not_one {a : F} (ha : a ≠ 0) :
    quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1 :=
  ⟨fun h ↦ by rw [h]; omega, fun h₂ ↦ (or_iff_right h₂).mp (quadraticChar_dichotomy ha)⟩
theorem quadraticChar_neg_one_iff_not_isSquare {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a := by
  by_cases ha : a = 0
  · simp only [ha, MulChar.map_zero, zero_eq_neg, one_ne_zero, isSquare_zero, not_true]
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]
theorem quadraticChar_exists_neg_one (hF : ringChar F ≠ 2) : ∃ a, quadraticChar F a = -1 :=
  (FiniteField.exists_nonsquare hF).imp fun _ h₁ ↦ quadraticChar_neg_one_iff_not_isSquare.mpr h₁
lemma quadraticChar_exists_neg_one' (hF : ringChar F ≠ 2) : ∃ a : Fˣ, quadraticChar F a = -1 := by
  refine (fun ⟨a, ha⟩ ↦ ⟨IsUnit.unit ?_, ha⟩) (quadraticChar_exists_neg_one hF)
  contrapose ha
  exact ne_of_eq_of_ne ((quadraticChar F).map_nonunit ha) (mt zero_eq_neg.mp one_ne_zero)
theorem quadraticChar_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 :=
  quadraticCharFun_eq_one_of_char_two hF ha
theorem quadraticChar_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 :=
  quadraticCharFun_eq_pow_of_char_ne_two hF ha
theorem quadraticChar_eq_pow_of_char_ne_two' (hF : ringChar F ≠ 2) (a : F) :
    (quadraticChar F a : F) = a ^ (Fintype.card F / 2) := by
  by_cases ha : a = 0
  · have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card two_pos
    simp only [ha, quadraticChar_apply, quadraticCharFun_zero, Int.cast_zero, zero_pow this.ne']
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    by_cases ha' : a ^ (Fintype.card F / 2) = 1
    · simp only [ha', if_true, Int.cast_one]
    · have ha'' := Or.resolve_left (FiniteField.pow_dichotomy hF ha) ha'
      simp only [ha'', Int.cast_ite, Int.cast_one, Int.cast_neg, ite_eq_right_iff]
      exact Eq.symm
variable (F)
theorem quadraticChar_isQuadratic : (quadraticChar F).IsQuadratic := by
  intro a
  by_cases ha : a = 0
  · left; rw [ha]; exact quadraticChar_zero
  · right; exact quadraticChar_dichotomy ha
variable {F}
theorem quadraticChar_ne_one (hF : ringChar F ≠ 2) : quadraticChar F ≠ 1 := by
  rcases quadraticChar_exists_neg_one' hF with ⟨a, ha⟩
  intro hχ
  simp only [hχ, one_apply a.isUnit, one_ne_zero, reduceCtorEq] at ha
set_option linter.deprecated false in
@[deprecated quadraticChar_ne_one (since := "2024-06-16")]
theorem quadraticChar_isNontrivial (hF : ringChar F ≠ 2) : (quadraticChar F).IsNontrivial :=
  (isNontrivial_iff _).mpr <| quadraticChar_ne_one hF
open Finset in
theorem quadraticChar_card_sqrts (hF : ringChar F ≠ 2) (a : F) :
    #{x : F | x ^ 2 = a}.toFinset = quadraticChar F a + 1 := by
  by_cases h₀ : a = 0
  · simp only [h₀, sq_eq_zero_iff, Set.setOf_eq_eq_singleton, Set.toFinset_card,
    Set.card_singleton, Int.ofNat_succ, Int.ofNat_zero, MulChar.map_zero]
  · set s := {x : F | x ^ 2 = a}.toFinset
    by_cases h : IsSquare a
    · rw [(quadraticChar_one_iff_isSquare h₀).mpr h]
      rcases h with ⟨b, h⟩
      rw [h, mul_self_eq_zero] at h₀
      have h₁ : s = [b, -b].toFinset := by
        ext1
        rw [← pow_two] at h
        simp only [Set.toFinset_setOf, h, mem_filter, mem_univ, true_and, List.toFinset_cons,
          List.toFinset_nil, insert_emptyc_eq, mem_insert, mem_singleton, s]
        exact sq_eq_sq_iff_eq_or_eq_neg
      norm_cast
      rw [h₁, List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
      exact card_pair (Ne.symm (mt (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀))
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr h]
      simp only [neg_add_cancel, Int.natCast_eq_zero, card_eq_zero]
      ext1
      simp only [(Set.mem_toFinset), Set.mem_setOf, not_mem_empty, iff_false]
      rw [isSquare_iff_exists_sq] at h
      exact fun h' ↦ h ⟨_, h'.symm⟩
theorem quadraticChar_sum_zero (hF : ringChar F ≠ 2) : ∑ a : F, quadraticChar F a = 0 :=
  sum_eq_zero_of_ne_one (quadraticChar_ne_one hF)
end quadraticChar
section SpecialValues
open ZMod MulChar
variable {F : Type*} [Field F] [Fintype F]
theorem quadraticChar_neg_one [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F (-1) = χ₄ (Fintype.card F) := by
  have h := quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  rw [h, χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  generalize Fintype.card F / 2 = n
  cases' Nat.even_or_odd n with h₂ h₂
  · simp only [Even.neg_one_pow h₂, if_true]
  · simp only [Odd.neg_one_pow h₂, Ring.neg_one_ne_one_of_char_ne_two hF, ite_false]
theorem FiniteField.isSquare_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
  classical 
  by_cases hF : ringChar F = 2
  · simp only [FiniteField.isSquare_of_char_two hF, Ne, true_iff]
    exact fun hf ↦
      one_ne_zero <|
        (Nat.odd_of_mod_four_eq_three hf).symm.trans <| FiniteField.even_card_of_char_two hF
  · have h₁ := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F)),
      quadraticChar_neg_one hF, χ₄_nat_eq_if_mod_four, h₁]
    simp only [Nat.one_ne_zero, if_false, ite_eq_left_iff, (by omega : (-1 : ℤ) ≠ 1), imp_false,
      not_not, Ne, reduceCtorEq]
    exact ⟨fun h ↦ ne_of_eq_of_ne h (by omega), (Nat.odd_mod_four_iff.mp h₁).resolve_right⟩
end SpecialValues