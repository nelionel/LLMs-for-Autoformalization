import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Opposite
section
variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module S M]
@[ext high]
theorem LinearMap.ext_ring_op
    {σ : Rᵐᵒᵖ →+* S} {f g : R →ₛₗ[σ] M} (h : f (1 : R) = g (1 : R)) :
    f = g :=
  ext fun x ↦ by
    rw [← one_mul x, ← op_smul_eq_mul]
    refine (f.map_smulₛₗ (MulOpposite.op x) 1).trans ?_
    rw [h]
    exact (g.map_smulₛₗ (MulOpposite.op x) 1).symm
end
namespace MulOpposite
universe u v
variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }
@[simp]
theorem coe_opLinearEquiv : (opLinearEquiv R : M → Mᵐᵒᵖ) = op :=
  rfl
@[simp]
theorem coe_opLinearEquiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ → M) = unop :=
  rfl
@[simp]
theorem coe_opLinearEquiv_toLinearMap : ((opLinearEquiv R).toLinearMap : M → Mᵐᵒᵖ) = op :=
  rfl
@[simp]
theorem coe_opLinearEquiv_symm_toLinearMap :
    ((opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ → M) = unop :=
  rfl
theorem opLinearEquiv_toAddEquiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv :=
  rfl
@[simp]
theorem coe_opLinearEquiv_addEquiv : ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ) = opAddEquiv :=
  rfl
theorem opLinearEquiv_symm_toAddEquiv :
    (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm :=
  rfl
@[simp]
theorem coe_opLinearEquiv_symm_addEquiv :
    ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm : Mᵐᵒᵖ ≃+ M) = opAddEquiv.symm :=
  rfl
end MulOpposite