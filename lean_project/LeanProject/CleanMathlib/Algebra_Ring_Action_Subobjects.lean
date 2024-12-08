import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.DistribMulAction
import Mathlib.Algebra.Ring.Action.Basic
variable {M G R : Type*}
variable [Monoid M] [Group G] [Semiring R]
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  { inferInstanceAs (DistribMulAction H R), inferInstanceAs (MulDistribMulAction H R) with }
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  H.toSubmonoid.mulSemiringAction