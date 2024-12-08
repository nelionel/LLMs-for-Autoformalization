import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.LinearAlgebra.SymplecticGroup
universe u₁ u₂
namespace LieAlgebra
open Matrix
open scoped Matrix
variable (n p q l : Type*) (R : Type u₂)
variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]
variable [CommRing R]
@[simp]
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace ⁅X, Y⁆ = 0 :=
  calc
    _ = Matrix.trace (X * Y) - Matrix.trace (Y * X) := trace_sub _ _
    _ = Matrix.trace (X * Y) - Matrix.trace (X * Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _
namespace SpecialLinear
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
    lie_mem' := fun _ _ => LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ _ _ }
theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val :=
  rfl
section ElementaryBasis
variable {n} [Fintype n] (i j : n)
def Eb (h : j ≠ i) : sl n R :=
  ⟨Matrix.stdBasisMatrix i j (1 : R),
    show Matrix.stdBasisMatrix i j (1 : R) ∈ LinearMap.ker (Matrix.traceLinearMap n R R) from
      Matrix.StdBasisMatrix.trace_zero i j (1 : R) h⟩
@[simp]
theorem eb_val (h : j ≠ i) : (Eb R i j h).val = Matrix.stdBasisMatrix i j 1 :=
  rfl
end ElementaryBasis
theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian (sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨j, i, hij⟩
  let A := Eb R i j hij
  let B := Eb R j i hij.symm
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero, ← sl_bracket, c.trivial, ZeroMemClass.coe_zero]
  simpa [A, B, stdBasisMatrix, Matrix.mul_apply, hij] using congr_fun (congr_fun c' i) i
end SpecialLinear
namespace Symplectic
def sp [Fintype l] : LieSubalgebra R (Matrix (l ⊕ l) (l ⊕ l) R) :=
  skewAdjointMatricesLieSubalgebra (Matrix.J l R)
end Symplectic
namespace Orthogonal
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)
@[simp]
theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ so n R ↔ Aᵀ = -A := by
  rw [so, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]
def indefiniteDiagonal : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => -1
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (p ⊕ q) (p ⊕ q) R) :=
  skewAdjointMatricesLieSubalgebra <| indefiniteDiagonal p q R
def Pso (i : R) : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => i
variable [Fintype p] [Fintype q]
theorem pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨x⟩|⟨x⟩ <;> rcases y with ⟨y⟩|⟨y⟩
  · 
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · 
    simp [Pso, indefiniteDiagonal]
  · 
    simp [Pso, indefiniteDiagonal]
  · 
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, hi, one_apply]
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)
theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i = 1 := by
  ext (x y); rcases x with ⟨x⟩|⟨x⟩ <;> rcases y with ⟨y⟩|⟨y⟩
  · 
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · 
    simp [Pso, indefiniteDiagonal]
  · 
    simp [Pso, indefiniteDiagonal]
  · 
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, hi, one_apply]
noncomputable def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (p ⊕ q) R := by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl
theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (p ⊕ q) (p ⊕ q) R) =
      (Pso p q R i)⁻¹ * (A : Matrix (p ⊕ q) (p ⊕ q) R) * Pso p q R i := by
  rw [soIndefiniteEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  erw [skewAdjointMatricesLieSubalgebraEquiv_apply]
def JD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 1 1 0
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)
def PD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 1 (-1) 1 1
def S :=
  indefiniteDiagonal l l R
theorem s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl
theorem jd_transform [Fintype l] : (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R := by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h, PD, s_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  simp [two_smul]
theorem pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟ (2 : R) • (PD l R)ᵀ = 1 := by
  rw [PD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]
  simp
instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertibleOfRightInverse _ _ (pd_inv l R)
noncomputable def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jd_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl
def JB :=
  Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)
def PB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)
variable [Fintype l]
theorem pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟ (PD l R)) = 1 := by
  rw [PB, Matrix.fromBlocks_multiply, mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]
instance invertiblePB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertibleOfRightInverse _ _ (pb_inv l R)
theorem jb_transform : (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) := by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Unit ⊕ l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) := by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, eq_self_iff_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
      DMatrix.zero_apply, Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr,
      Sum.elim_inr, Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff, reduceCtorEq] <;>
    congr 1
noncomputable def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Unit ⊕ l) l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ _ (Equiv.sumAssoc PUnit l l))
        (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jb_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    LieSubalgebra.mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simp [indefiniteDiagonal_assoc, S]
end Orthogonal
end LieAlgebra