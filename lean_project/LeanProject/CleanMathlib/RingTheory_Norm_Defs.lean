import Mathlib.LinearAlgebra.Determinant
universe u v w
variable {R S : Type*} [CommRing R] [Ring S]
variable [Algebra R S]
variable {K : Type*} [Field K]
variable {ι : Type w}
open Module
open LinearMap
open Matrix Polynomial
open scoped Matrix
namespace Algebra
variable (R)
@[stacks 0BIF "Norm"]
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom
theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) := rfl
theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) :
    norm R x = 1 := by rw [norm_apply, LinearMap.det]; split_ifs <;> trivial
variable {R}
theorem norm_eq_one_of_not_module_finite (h : ¬Module.Finite R S) (x : S) : norm R x = 1 := by
  refine norm_eq_one_of_not_exists_basis _ (mt ?_ h) _
  rintro ⟨s, ⟨b⟩⟩
  exact Module.Finite.of_basis b
theorem norm_eq_matrix_det [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) := by
  rw [norm_apply, ← LinearMap.det_toMatrix b, ← toMatrix_lmul_eq]; rfl
theorem norm_algebraMap_of_basis [Fintype ι] (b : Basis ι R S) (x : R) :
    norm R (algebraMap R S x) = x ^ Fintype.card ι := by
  haveI := Classical.decEq ι
  rw [norm_apply, ← det_toMatrix b, lmul_algebraMap]
  convert @det_diagonal _ _ _ _ _ fun _ : ι => x
  · ext (i j); rw [toMatrix_lsmul]
  · rw [Finset.prod_const, Finset.card_univ]
@[simp]
protected theorem norm_algebraMap {L : Type*} [Ring L] [Algebra K L] (x : K) :
    norm K (algebraMap K L x) = x ^ finrank K L := by
  by_cases H : ∃ s : Finset L, Nonempty (Basis s K L)
  · rw [norm_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zero]
    rintro ⟨s, ⟨b⟩⟩
    exact H ⟨s, ⟨b⟩⟩
end Algebra