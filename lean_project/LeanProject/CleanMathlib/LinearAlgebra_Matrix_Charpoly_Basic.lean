import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PolynomialAlgebra
noncomputable section
universe u v w
namespace Matrix
open Finset Matrix Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]
variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)
variable (i j : n)
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
theorem charmatrix_apply :
    charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j - C (M i j) :=
  rfl
@[simp]
theorem charmatrix_apply_eq : charmatrix M i i = (X : R[X]) - C (M i i) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]
@[simp]
theorem charmatrix_apply_ne (h : i ≠ j) : charmatrix M i j = -C (M i j) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]
theorem matPolyEquiv_charmatrix : matPolyEquiv (charmatrix M) = X - C M := by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub, Pi.sub_apply]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq, coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]
theorem charmatrix_reindex (e : n ≃ m) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]
lemma charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    charmatrix (M.map f) = (charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, charmatrix, diagonal]
lemma charmatrix_fromBlocks :
    charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (charmatrix M₁₁) (- M₁₂.map C) (- M₂₁.map C) (charmatrix M₂₂) := by
  simp only [charmatrix]
  ext (i|i) (j|j) : 2 <;> simp [diagonal]
@[simp]
lemma charmatrix_blockTriangular_iff {α : Type*} [Preorder α] {M : Matrix n n R} {b : n → α} :
    M.charmatrix.BlockTriangular b ↔ M.BlockTriangular b := by
  rw [charmatrix, scalar_apply, RingHom.mapMatrix_apply, (blockTriangular_diagonal _).sub_iff_right]
  simp [BlockTriangular]
alias ⟨BlockTriangular.of_charmatrix, BlockTriangular.charmatrix⟩ := charmatrix_blockTriangular_iff
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det
theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex, Matrix.det_reindex_self]
lemma charpoly_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpoly = M.charpoly.map f := by
  rw [charpoly, charmatrix_map, ← Polynomial.coe_mapRingHom, charpoly, RingHom.map_det,
    RingHom.mapMatrix_apply]
@[simp]
lemma charpoly_fromBlocks_zero₁₂ :
    (fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]
@[simp]
lemma charpoly_fromBlocks_zero₂₁ :
    (fromBlocks M₁₁ M₁₂ 0 M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]
lemma charmatrix_toSquareBlock {α : Type*} [DecidableEq α] {b : n → α} {a : α} :
    (M.toSquareBlock b a).charmatrix = M.charmatrix.toSquareBlock b a := by
  ext i j : 1
  simp [charmatrix_apply, toSquareBlock_def, diagonal_apply, Subtype.ext_iff]
lemma BlockTriangular.charpoly {α : Type*} {b : n → α} [LinearOrder α] (h : M.BlockTriangular b) :
    M.charpoly = ∏ a ∈ image b univ, (M.toSquareBlock b a).charpoly := by
  simp only [Matrix.charpoly, h.charmatrix.det, charmatrix_toSquareBlock]
lemma charpoly_of_upperTriangular [LinearOrder n] (M : Matrix n n R) (h : M.BlockTriangular id) :
    M.charpoly = ∏ i : n, (X - C (M i i)) := by
  simp [charpoly, det_of_upperTriangular h.charmatrix]
theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  apply_fun matPolyEquiv at h
  simp only [_root_.map_mul, matPolyEquiv_charmatrix] at h
  apply_fun fun p => p.eval M at h
  rw [eval_mul_X_sub_C] at h
  rw [matPolyEquiv_smul_one, eval_map] at h
  exact h
end Matrix