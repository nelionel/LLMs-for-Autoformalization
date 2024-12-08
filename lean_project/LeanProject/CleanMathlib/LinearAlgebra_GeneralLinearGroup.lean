import Mathlib.Algebra.Module.Equiv.Basic
variable (R M : Type*)
namespace LinearMap
variable [Semiring R] [AddCommMonoid M] [Module R M]
abbrev GeneralLinearGroup :=
  (M →ₗ[R] M)ˣ
namespace GeneralLinearGroup
variable {R M}
def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with
    invFun := f.inv.toFun
    left_inv := fun m ↦ show (f.inv * f.val) m = m by rw [f.inv_val]; simp
    right_inv := fun m ↦ show (f.val * f.inv) m = m by rw [f.val_inv]; simp }
def ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where
  val := f
  inv := (f.symm : M →ₗ[R] M)
  val_inv := LinearMap.ext fun _ ↦ f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ ↦ f.symm_apply_apply _
variable (R M)
def generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  toFun := toLinearEquiv
  invFun := ofLinearEquiv
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_mul' x y := by ext; rfl
@[simp]
theorem generalLinearEquiv_to_linearMap (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f : M →ₗ[R] M) = f := by ext; rfl
@[simp]
theorem coeFn_generalLinearEquiv (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f) = (f : M → M) := rfl
end GeneralLinearGroup
end LinearMap