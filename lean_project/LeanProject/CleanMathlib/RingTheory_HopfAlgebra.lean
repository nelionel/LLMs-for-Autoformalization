import Mathlib.RingTheory.Bialgebra.Basic
suppress_compilation
universe u v
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Bialgebra R A where
  antipode : A →ₗ[R] A
  mul_antipode_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  mul_antipode_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
namespace HopfAlgebra
variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
@[simp]
theorem mul_antipode_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A (antipode.rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_rTensor_comul a
@[simp]
theorem mul_antipode_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A (antipode.lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_lTensor_comul a
open Coalgebra
@[simp]
lemma sum_antipode_mul_eq {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode (R := R) (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)
@[simp]
lemma sum_mul_antipode_eq {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode (R := R) (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)
lemma sum_antipode_mul_eq_smul {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode (R := R) (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq, Algebra.smul_def, mul_one]
lemma sum_mul_antipode_eq_smul {a : A} (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode (R := R) (repr.right i) =
      counit (R := R) a • 1 := by
  rw [sum_mul_antipode_eq, Algebra.smul_def, mul_one]
end HopfAlgebra
namespace CommSemiring
variable (R : Type u) [CommSemiring R]
open HopfAlgebra
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp
@[simp]
theorem antipode_eq_id : antipode (R := R) (A := R) = .id := rfl
end CommSemiring