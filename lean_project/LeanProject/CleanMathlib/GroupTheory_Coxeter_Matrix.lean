import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
@[ext]
structure CoxeterMatrix (B : Type*) where
  M : Matrix B B ℕ
  isSymm : M.IsSymm := by decide
  diagonal i : M i i = 1 := by decide
  off_diagonal i i' : i ≠ i' → M i i' ≠ 1 := by decide
namespace CoxeterMatrix
variable {B : Type*}
instance : CoeFun (CoxeterMatrix B) fun _ ↦ (Matrix B B ℕ) := ⟨M⟩
variable {B' : Type*} (e : B ≃ B') (M : CoxeterMatrix B)
attribute [simp] diagonal
theorem symmetric (i i' : B) : M i i' = M i' i := M.isSymm.apply i' i
protected def reindex : CoxeterMatrix B' where
  M := Matrix.reindex e e M
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal (e.symm i)
  off_diagonal i i' h := M.off_diagonal (e.symm i) (e.symm i') (e.symm.injective.ne h)
theorem reindex_apply (i i' : B') : M.reindex e i i' = M (e.symm i) (e.symm i') := rfl
variable (n : ℕ)
def Aₙ : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n ↦
    if i = j then 1
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop
def Bₙ : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n ↦
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 4
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop
def Dₙ : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n ↦
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then 3
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop
def I₂ₘ (m : ℕ) : CoxeterMatrix (Fin 2) where
  M := Matrix.of fun i j => if i = j then 1 else m + 2
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by simp
def E₆ : CoxeterMatrix (Fin 6) where
  M := !![1, 2, 3, 2, 2, 2;
          2, 1, 2, 3, 2, 2;
          3, 2, 1, 3, 2, 2;
          2, 3, 3, 1, 3, 2;
          2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 3, 1]
def E₇ : CoxeterMatrix (Fin 7) where
  M := !![1, 2, 3, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2;
          2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 3, 1]
def E₈ : CoxeterMatrix (Fin 8) where
  M := !![1, 2, 3, 2, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 2, 3, 1]
def F₄ : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 2;
          3, 1, 4, 2;
          2, 4, 1, 3;
          2, 2, 3, 1]
def G₂ : CoxeterMatrix (Fin 2) where
  M := !![1, 6;
          6, 1]
def H₃ : CoxeterMatrix (Fin 3) where
  M := !![1, 3, 2;
          3, 1, 5;
          2, 5, 1]
def H₄ : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 2;
          3, 1, 3, 2;
          2, 3, 1, 5;
          2, 2, 5, 1]
end CoxeterMatrix