import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.StdBasis
namespace Basis
variable {ι R M : Type*} (m n : Type*)
variable [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid M] [Module R M]
protected noncomputable def matrix (b : Basis ι R M) :
    Basis (m × n × ι) R (Matrix m n M) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basis fun _ : n => b)
    ((Equiv.sigmaEquivProd _ _).trans <| .prodCongr (.refl _) (Equiv.sigmaEquivProd _ _))
    |>.map (Matrix.ofLinearEquiv R)
variable {n m}
@[simp]
theorem matrix_apply (b : Basis ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [DecidableEq n] :
    b.matrix m n (i, j, k) = Matrix.stdBasisMatrix i j (b k) := by
  simp [Basis.matrix, Matrix.stdBasisMatrix_eq_of_single_single]
end Basis
namespace Matrix
variable (R : Type*) (m n : Type*) [Fintype m] [Finite n] [Semiring R]
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
    |>.map (ofLinearEquiv R)
variable {n m}
theorem stdBasis_eq_stdBasisMatrix (i : m) (j : n) [DecidableEq m] [DecidableEq n] :
    stdBasis R m n (i, j) = stdBasisMatrix i j (1 : R) := by
  simp [stdBasis, stdBasisMatrix_eq_of_single_single]
end Matrix