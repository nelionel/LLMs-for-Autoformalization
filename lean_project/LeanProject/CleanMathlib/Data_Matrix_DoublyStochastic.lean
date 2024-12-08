import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
open Finset Function Matrix
variable {R n : Type*} [Fintype n] [DecidableEq n]
section OrderedSemiring
variable [OrderedSemiring R] {M : Matrix n n R}
def doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [OrderedSemiring R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]
lemma mem_doublyStochastic :
    M ∈ doublyStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 :=
  Iff.rfl
lemma mem_doublyStochastic_iff_sum :
    M ∈ doublyStochastic R n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1 := by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]
lemma nonneg_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _
lemma sum_row_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.1 _
lemma sum_col_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (j : n) : ∑ i, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.2 _
lemma mulVec_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_doublyStochastic.1 hM).2.1
lemma one_vecMul_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_doublyStochastic.1 hM).2.2
lemma le_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← sum_row_of_mem_doublyStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)
lemma convex_doublyStochastic : Convex R (doublyStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]
lemma permMatrix_mem_doublyStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ doublyStochastic R n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2, ?g3⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]
  case g3 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply]
end OrderedSemiring
section LinearOrderedSemifield
variable [LinearOrderedSemifield R]
lemma exists_mem_doublyStochastic_eq_smul_iff {M : Matrix n n R} {s : R} (hs : 0 ≤ s) :
    (∃ M' ∈ doublyStochastic R n, M = s • M') ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) := by
  classical
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hM'
    simp only [smul_apply, smul_eq_mul, ← mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
    ext i j
    specialize h₂ i
    rw [sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    exact h₂ _ (by simp)
  rintro ⟨hM₁, hM₂, hM₃⟩
  exact ⟨s⁻¹ • M, by simp [mem_doublyStochastic_iff_sum, ← mul_sum, hs.ne', inv_mul_cancel₀, *]⟩
end LinearOrderedSemifield