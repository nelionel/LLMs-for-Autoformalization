import Mathlib.Algebra.Ring.AddAut
import Mathlib.Data.ZMod.Basic
namespace ZMod
variable (n : ℕ)
@[simps]
def AddAutEquivUnits : AddAut (ZMod n) ≃* (ZMod n)ˣ :=
  have h (f : AddAut (ZMod n)) (x : ZMod n) : f 1 * x = f x := by
    rw [mul_comm, ← x.intCast_zmod_cast, ← zsmul_eq_mul, ← map_zsmul, zsmul_one]
  { toFun := fun f ↦ Units.mkOfMulEqOne (f 1) (f⁻¹ 1) ((h f _).trans (f.inv_apply_self _ _))
    invFun := AddAut.mulLeft
    left_inv := fun f ↦ by simp [DFunLike.ext_iff, Units.smul_def, h]
    right_inv := fun x ↦ by simp [Units.ext_iff, Units.smul_def]
    map_mul' := fun f g ↦ by simp [Units.ext_iff, h] }
end ZMod