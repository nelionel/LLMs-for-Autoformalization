import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.TensorProduct.Basic
open scoped TensorProduct
open Module
noncomputable section
universe u v w
namespace Subalgebra
variable {R : Type u} {S : Type v}
section Semiring
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable (A : Subalgebra R S)
def lTensorBot : (⊥ : Subalgebra R S) ⊗[R] A ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).lTensorOne ?_ ?_
  · rintro x y a b
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx, ← hy, ← map_mul]
    erw [(toSubmodule A).lTensorOne_tmul x' a,
      (toSubmodule A).lTensorOne_tmul y' b,
      (toSubmodule A).lTensorOne_tmul (x' * y') (a * b)]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm x' y']
  · exact Submodule.lTensorOne_one_tmul _
variable {A}
@[simp]
theorem lTensorBot_tmul (x : R) (a : A) : A.lTensorBot (algebraMap R _ x ⊗ₜ[R] a) = x • a :=
  (toSubmodule A).lTensorOne_tmul x a
@[simp]
theorem lTensorBot_one_tmul (a : A) : A.lTensorBot (1 ⊗ₜ[R] a) = a :=
  (toSubmodule A).lTensorOne_one_tmul a
@[simp]
theorem lTensorBot_symm_apply (a : A) : A.lTensorBot.symm a = 1 ⊗ₜ[R] a := rfl
variable (A)
def rTensorBot : A ⊗[R] (⊥ : Subalgebra R S) ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).rTensorOne ?_ ?_
  · rintro a b x y
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx, ← hy, ← map_mul]
    erw [(toSubmodule A).rTensorOne_tmul x' a,
      (toSubmodule A).rTensorOne_tmul y' b,
      (toSubmodule A).rTensorOne_tmul (x' * y') (a * b)]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, mul_comm x' y']
  · exact Submodule.rTensorOne_tmul_one _
variable {A}
@[simp]
theorem rTensorBot_tmul (x : R) (a : A) : A.rTensorBot (a ⊗ₜ[R] algebraMap R _ x) = x • a :=
  (toSubmodule A).rTensorOne_tmul x a
@[simp]
theorem rTensorBot_tmul_one (a : A) : A.rTensorBot (a ⊗ₜ[R] 1) = a :=
  (toSubmodule A).rTensorOne_tmul_one a
@[simp]
theorem rTensorBot_symm_apply (a : A) : A.rTensorBot.symm a = a ⊗ₜ[R] 1 := rfl
variable (A)
@[simp]
theorem comm_trans_lTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.lTensorBot = A.rTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_lTensorOne
@[simp]
theorem comm_trans_rTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.rTensorBot = A.lTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_rTensorOne
end Semiring
section CommSemiring
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (A B : Subalgebra R S)
def mulMap : A ⊗[R] B →ₐ[R] S := Algebra.TensorProduct.productMap A.val B.val
@[simp]
theorem mulMap_tmul (a : A) (b : B) : mulMap A B (a ⊗ₜ[R] b) = a.1 * b.1 := rfl
theorem mulMap_toLinearMap : (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B) :=
  rfl
theorem mulMap_comm : mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A) := by
  ext <;> simp
theorem mulMap_range : (A.mulMap B).range = A ⊔ B := by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]
theorem mulMap_bot_left_eq : mulMap ⊥ A = A.val.comp A.lTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_left_eq
theorem mulMap_bot_right_eq : mulMap A ⊥ = A.val.comp A.rTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_right_eq
def mulMap' : A ⊗[R] B →ₐ[R] ↥(A ⊔ B) :=
  (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict
variable {A B} in
@[simp]
theorem val_mulMap'_tmul (a : A) (b : B) : (mulMap' A B (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl
theorem mulMap'_surjective : Function.Surjective (mulMap' A B) := by
  simp_rw [mulMap', AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]
end CommSemiring
end Subalgebra