import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Equiv
section Semiring
variable (G : Type*) [Group G]
variable (R : Type*) [Semiring R]
@[simps!]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
end Semiring