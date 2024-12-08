import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Lie.Basic
open Matrix
variable {R : Type*} [CommRing R]
def crossProduct : (Fin 3 → R) →ₗ[R] (Fin 3 → R) →ₗ[R] Fin 3 → R := by
  apply LinearMap.mk₂ R fun a b : Fin 3 → R =>
      ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, smul_mul_assoc]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, mul_smul_comm]
scoped[Matrix] infixl:74 " ×₃ " => crossProduct
theorem cross_apply (a b : Fin 3 → R) :
    a ×₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := rfl
section ProductsProperties
@[simp]
theorem cross_anticomm (v w : Fin 3 → R) : -(v ×₃ w) = w ×₃ v := by
  simp [cross_apply, mul_comm]
alias neg_cross := cross_anticomm
@[simp]
theorem cross_anticomm' (v w : Fin 3 → R) : v ×₃ w + w ×₃ v = 0 := by
  rw [add_eq_zero_iff_eq_neg, cross_anticomm]
@[simp]
theorem cross_self (v : Fin 3 → R) : v ×₃ v = 0 := by
  simp [cross_apply, mul_comm]
@[simp 1100] 
theorem dot_self_cross (v w : Fin 3 → R) : v ⬝ᵥ v ×₃ w = 0 := by
  rw [cross_apply, vec3_dotProduct]
  norm_num
  ring
@[simp 1100] 
theorem dot_cross_self (v w : Fin 3 → R) : w ⬝ᵥ v ×₃ w = 0 := by
  rw [← cross_anticomm, Matrix.dotProduct_neg, dot_self_cross, neg_zero]
theorem triple_product_permutation (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = v ⬝ᵥ w ×₃ u := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring
theorem triple_product_eq_det (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = Matrix.det ![u, v, w] := by
  rw [vec3_dotProduct, cross_apply, det_fin_three]
  norm_num
  ring
theorem cross_dot_cross (u v w x : Fin 3 → R) :
    u ×₃ v ⬝ᵥ w ×₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring
end ProductsProperties
section LeibnizProperties
theorem leibniz_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) = u ×₃ v ×₃ w + v ×₃ (u ×₃ w) := by
  simp_rw [cross_apply, vec3_add]
  apply vec3_eq <;> norm_num <;> ring
def Cross.lieRing : LieRing (Fin 3 → R) :=
  { Pi.addCommGroup with
    bracket := fun u v => u ×₃ v
    add_lie := LinearMap.map_add₂ _
    lie_add := fun _ => LinearMap.map_add _
    lie_self := cross_self
    leibniz_lie := leibniz_cross }
attribute [local instance] Cross.lieRing
theorem cross_cross (u v w : Fin 3 → R) : u ×₃ v ×₃ w = u ×₃ (v ×₃ w) - v ×₃ (u ×₃ w) :=
  lie_lie u v w
theorem jacobi_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
  lie_jacobi u v w
end LeibnizProperties
lemma crossProduct_ne_zero_iff_linearIndependent {F : Type*} [Field F] {v w : Fin 3 → F} :
    crossProduct v w ≠ 0 ↔ LinearIndependent F ![v, w] := by
  rw [not_iff_comm]
  by_cases hv : v = 0
  · rw [hv, map_zero, LinearMap.zero_apply, eq_self, iff_true]
    exact fun h ↦ h.ne_zero 0 rfl
  constructor
  · rw [LinearIndependent.pair_iff' hv, not_forall_not]
    rintro ⟨a, rfl⟩
    rw [LinearMap.map_smul, cross_self, smul_zero]
  have hv' : v = ![v 0, v 1, v 2] := by simp [← List.ofFn_inj]
  have hw' : w = ![w 0, w 1, w 2] := by simp [← List.ofFn_inj]
  intro h1 h2
  simp_rw [cross_apply, cons_eq_zero_iff, zero_empty, and_true, sub_eq_zero] at h1
  have h20 := LinearIndependent.pair_iff.mp h2 (- w 0) (v 0)
  have h21 := LinearIndependent.pair_iff.mp h2 (- w 1) (v 1)
  have h22 := LinearIndependent.pair_iff.mp h2 (- w 2) (v 2)
  rw [neg_smul, neg_add_eq_zero, hv', hw', smul_vec3, smul_vec3, ← hv', ← hw'] at h20 h21 h22
  simp only [smul_eq_mul, mul_comm (w 0), mul_comm (w 1), mul_comm (w 2), h1] at h20 h21 h22
  rw [hv', cons_eq_zero_iff, cons_eq_zero_iff, cons_eq_zero_iff, zero_empty] at hv
  exact hv ⟨(h20 trivial).2, (h21 trivial).2, (h22 trivial).2, rfl⟩