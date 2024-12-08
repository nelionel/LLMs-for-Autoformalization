import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
namespace Matrix
variable {m R A : Type*} [Fintype m] [CommRing R]
def Nondegenerate (M : Matrix m m R) :=
  ∀ v, (∀ w, Matrix.dotProduct v (M *ᵥ w) = 0) → v = 0
theorem Nondegenerate.eq_zero_of_ortho {M : Matrix m m R} (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, Matrix.dotProduct v (M *ᵥ w) = 0) : v = 0 :=
  hM v hv
theorem Nondegenerate.exists_not_ortho_of_ne_zero {M : Matrix m m R} (hM : Nondegenerate M)
    {v : m → R} (hv : v ≠ 0) : ∃ w, Matrix.dotProduct v (M *ᵥ w) ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)
variable [CommRing A] [IsDomain A]
theorem nondegenerate_of_det_ne_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) :
    Nondegenerate M := by
  intro v hv
  ext i
  specialize hv (M.cramer (Pi.single i 1))
  refine (mul_eq_zero.mp ?_).resolve_right hM
  convert hv
  simp only [mulVec_cramer M (Pi.single i 1), dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i, Pi.single_eq_same, mul_one]
  · intro j _ hj
    simp [hj]
  · intros
    have := Finset.mem_univ i
    contradiction
theorem eq_zero_of_vecMul_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : v ᵥ* M = 0) : v = 0 :=
  (nondegenerate_of_det_ne_zero hM).eq_zero_of_ortho fun w => by
    rw [dotProduct_mulVec, hv, zero_dotProduct]
theorem eq_zero_of_mulVec_eq_zero [DecidableEq m] {M : Matrix m m A} (hM : M.det ≠ 0) {v : m → A}
    (hv : M *ᵥ v = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (by rwa [det_transpose]) ((vecMul_transpose M v).trans hv)
end Matrix