import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.End
namespace Submonoid
variable {M α : Type*} [Monoid M]
instance distribMulAction [AddMonoid α] [DistribMulAction M α] (S : Submonoid M) :
    DistribMulAction S α :=
  DistribMulAction.compHom _ S.subtype
instance mulDistribMulAction [Monoid α] [MulDistribMulAction M α] (S : Submonoid M) :
    MulDistribMulAction S α :=
  MulDistribMulAction.compHom _ S.subtype
end Submonoid