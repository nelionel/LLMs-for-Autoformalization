import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Equiv
abbrev RingAut (R : Type*) [Mul R] [Add R] :=
  RingEquiv R R
namespace RingAut
section mul_add
variable (R : Type*) [Mul R] [Add R]
instance : Group (RingAut R) where
  mul g h := RingEquiv.trans h g
  one := RingEquiv.refl R
  inv := RingEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := RingEquiv.self_trans_symm
instance : Inhabited (RingAut R) :=
  ⟨1⟩
def toAddAut : RingAut R →* AddAut R where
  toFun := RingEquiv.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
def toMulAut : RingAut R →* MulAut R where
  toFun := RingEquiv.toMulEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
def toPerm : RingAut R →* Equiv.Perm R where
  toFun := RingEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl
end mul_add
section Semiring
variable {G R : Type*} [Group G] [Semiring R]
instance applyMulSemiringAction :
    MulSemiringAction (RingAut R) R where
  smul := (· <| ·)
  smul_zero := RingEquiv.map_zero
  smul_add := RingEquiv.map_add
  smul_one := RingEquiv.map_one
  smul_mul := RingEquiv.map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
@[simp]
protected theorem smul_def (f : RingAut R) (r : R) : f • r = f r :=
  rfl
instance apply_faithfulSMul : FaithfulSMul (RingAut R) R :=
  ⟨RingEquiv.ext⟩
variable (G R)
@[simps]
def _root_.MulSemiringAction.toRingAut [MulSemiringAction G R] :
    G →* RingAut R where
  toFun := MulSemiringAction.toRingEquiv G R
  map_mul' g h := RingEquiv.ext <| mul_smul g h
  map_one' := RingEquiv.ext <| one_smul _
end Semiring
end RingAut