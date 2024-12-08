import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
open Equiv
variable {n R : Type*} [DecidableEq n] [Fintype n] (σ : Perm n)
variable (R) in
abbrev Equiv.Perm.permMatrix [Zero R] [One R] : Matrix n n R :=
  σ.toPEquiv.toMatrix
namespace Matrix
@[simp]
theorem det_permutation [CommRing R] : det (σ.permMatrix R) = Perm.sign σ := by
  rw [← Matrix.mul_one (σ.permMatrix R), PEquiv.toPEquiv_mul_matrix,
    det_permute, det_one, mul_one]
theorem trace_permutation [AddCommMonoidWithOne R] :
    trace (σ.permMatrix R) = (Function.fixedPoints σ).ncard := by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_Finset, Function.fixedPoints, Function.IsFixedPt]
end Matrix