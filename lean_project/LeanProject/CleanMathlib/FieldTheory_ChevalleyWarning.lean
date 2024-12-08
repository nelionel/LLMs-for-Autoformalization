import Mathlib.FieldTheory.Finite.Basic
universe u v
section FiniteField
open MvPolynomial
open Function hiding eval
open Finset FiniteField
variable {K σ ι : Type*} [Fintype K] [Field K] [Fintype σ] [DecidableEq σ]
local notation "q" => Fintype.card K
theorem MvPolynomial.sum_eval_eq_zero (f : MvPolynomial σ K)
    (h : f.totalDegree < (q - 1) * Fintype.card σ) : ∑ x, eval x f = 0 := by
  haveI : DecidableEq K := Classical.decEq K
  calc
    ∑ x, eval x f = ∑ x : σ → K, ∑ d ∈ f.support, f.coeff d * ∏ i, x i ^ d i := by
      simp only [eval_eq']
    _ = ∑ d ∈ f.support, ∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i := sum_comm
    _ = 0 := sum_eq_zero ?_
  intro d hd
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1 := f.exists_degree_lt (q - 1) h hd
  calc
    (∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i) = f.coeff d * ∑ x : σ → K, ∏ i, x i ^ d i :=
      (mul_sum ..).symm
    _ = 0 := (mul_eq_zero.mpr ∘ Or.inr) ?_
  calc
    (∑ x : σ → K, ∏ i, x i ^ d i) =
        ∑ x₀ : { j // j ≠ i } → K, ∑ x : { x : σ → K // x ∘ (↑) = x₀ }, ∏ j, (x : σ → K) j ^ d j :=
      (Fintype.sum_fiberwise _ _).symm
    _ = 0 := Fintype.sum_eq_zero _ ?_
  intro x₀
  let e : K ≃ { x // x ∘ ((↑) : _ → σ) = x₀ } := (Equiv.subtypeEquivCodomain _).symm
  calc
    (∑ x : { x : σ → K // x ∘ (↑) = x₀ }, ∏ j, (x : σ → K) j ^ d j) =
        ∑ a : K, ∏ j : σ, (e a : σ → K) j ^ d j := (e.sum_comp _).symm
    _ = ∑ a : K, (∏ j, x₀ j ^ d j) * a ^ d i := Fintype.sum_congr _ _ ?_
    _ = (∏ j, x₀ j ^ d j) * ∑ a : K, a ^ d i := by rw [mul_sum]
    _ = 0 := by rw [sum_pow_lt_card_sub_one K _ hi, mul_zero]
  intro a
  let e' : { j // j = i } ⊕ { j // j ≠ i } ≃ σ := Equiv.sumCompl _
  letI : Unique { j // j = i } :=
    { default := ⟨i, rfl⟩
      uniq := fun ⟨j, h⟩ => Subtype.val_injective h }
  calc
    (∏ j : σ, (e a : σ → K) j ^ d j) =
        (e a : σ → K) i ^ d i * ∏ j : { j // j ≠ i }, (e a : σ → K) j ^ d j := by
      rw [← e'.prod_comp, Fintype.prod_sum_type, univ_unique, prod_singleton]; rfl
    _ = a ^ d i * ∏ j : { j // j ≠ i }, (e a : σ → K) j ^ d j := by
      rw [Equiv.subtypeEquivCodomain_symm_apply_eq]
    _ = a ^ d i * ∏ j, x₀ j ^ d j := congr_arg _ (Fintype.prod_congr _ _ ?_)
    _ = (∏ j, x₀ j ^ d j) * a ^ d i := mul_comm _ _
  rintro ⟨j, hj⟩
  show (e a : σ → K) j ^ d j = x₀ ⟨j, hj⟩ ^ d j
  rw [Equiv.subtypeEquivCodomain_symm_apply_ne]
variable [DecidableEq K] (p : ℕ) [CharP K p]
theorem char_dvd_card_solutions_of_sum_lt {s : Finset ι} {f : ι → MvPolynomial σ K}
    (h : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } := by
  have hq : 0 < q - 1 := by rw [← Fintype.card_units, Fintype.card_pos_iff]; exact ⟨1⟩
  let S : Finset (σ → K) := {x | ∀ i ∈ s, eval x (f i) = 0}
  have hS (x : σ → K) : x ∈ S ↔ ∀ i ∈ s, eval x (f i) = 0 := by simp [S]
  let F : MvPolynomial σ K := ∏ i ∈ s, (1 - f i ^ (q - 1))
  have hF : ∀ x, eval x F = if x ∈ S then 1 else 0 := by
    intro x
    calc
      eval x F = ∏ i ∈ s, eval x (1 - f i ^ (q - 1)) := eval_prod s _ x
      _ = if x ∈ S then 1 else 0 := ?_
    simp only [(eval x).map_sub, (eval x).map_pow, (eval x).map_one]
    split_ifs with hx
    · apply Finset.prod_eq_one
      intro i hi
      rw [hS] at hx
      rw [hx i hi, zero_pow hq.ne', sub_zero]
    · obtain ⟨i, hi, hx⟩ : ∃ i ∈ s, eval x (f i) ≠ 0 := by
        simpa [hS, not_forall, Classical.not_imp] using hx
      apply Finset.prod_eq_zero hi
      rw [pow_card_sub_one_eq_one (eval x (f i)) hx, sub_self]
  have key : ∑ x, eval x F = Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } := by
    rw [Fintype.card_of_subtype S hS, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ←
      Fintype.sum_extend_by_zero S, sum_congr rfl fun x _ => hF x]
  show p ∣ Fintype.card { x // ∀ i : ι, i ∈ s → eval x (f i) = 0 }
  rw [← CharP.cast_eq_zero_iff K, ← key]
  show (∑ x, eval x F) = 0
  apply F.sum_eval_eq_zero
  show F.totalDegree < (q - 1) * Fintype.card σ
  calc
    F.totalDegree ≤ ∑ i ∈ s, (1 - f i ^ (q - 1)).totalDegree := totalDegree_finset_prod s _
    _ ≤ ∑ i ∈ s, (q - 1) * (f i).totalDegree := sum_le_sum fun i _ => ?_
    _ = (q - 1) * ∑ i ∈ s, (f i).totalDegree := (mul_sum ..).symm
    _ < (q - 1) * Fintype.card σ := by rwa [mul_lt_mul_left hq]
  show (1 - f i ^ (q - 1)).totalDegree ≤ (q - 1) * (f i).totalDegree
  calc
    (1 - f i ^ (q - 1)).totalDegree ≤
        max (1 : MvPolynomial σ K).totalDegree (f i ^ (q - 1)).totalDegree := totalDegree_sub _ _
    _ ≤ (f i ^ (q - 1)).totalDegree := by simp
    _ ≤ (q - 1) * (f i).totalDegree := totalDegree_pow _ _
theorem char_dvd_card_solutions_of_fintype_sum_lt [Fintype ι] {f : ι → MvPolynomial σ K}
    (h : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // ∀ i, eval x (f i) = 0 } := by
  simpa using char_dvd_card_solutions_of_sum_lt p h
theorem char_dvd_card_solutions {f : MvPolynomial σ K} (h : f.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // eval x f = 0 } := by
  let F : Unit → MvPolynomial σ K := fun _ => f
  have : (∑ i : Unit, (F i).totalDegree) < Fintype.card σ := h
  convert char_dvd_card_solutions_of_sum_lt p this
  aesop
theorem char_dvd_card_solutions_of_add_lt {f₁ f₂ : MvPolynomial σ K}
    (h : f₁.totalDegree + f₂.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // eval x f₁ = 0 ∧ eval x f₂ = 0 } := by
  let F : Bool → MvPolynomial σ K := fun b => cond b f₂ f₁
  have : (∑ b : Bool, (F b).totalDegree) < Fintype.card σ := (add_comm _ _).trans_lt h
  simpa only [Bool.forall_bool] using char_dvd_card_solutions_of_fintype_sum_lt p this
end FiniteField