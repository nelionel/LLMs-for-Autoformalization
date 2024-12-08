import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Group.Action.Pi
universe u v
variable {I : Type u}
variable {f : I → Type v}
instance Pi.noZeroSMulDivisors (α) [Zero α] [∀ i, Zero <| f i]
    [∀ i, SMulWithZero α <| f i] [∀ i, NoZeroSMulDivisors α <| f i] :
    NoZeroSMulDivisors α (∀ i : I, f i) :=
  ⟨fun {_ _} h =>
    or_iff_not_imp_left.mpr fun hc =>
      funext fun i => (smul_eq_zero.mp (congr_fun h i)).resolve_left hc⟩
instance _root_.Function.noZeroSMulDivisors {ι α β : Type*} [Zero α] [Zero β]
    [SMulWithZero α β] [NoZeroSMulDivisors α β] : NoZeroSMulDivisors α (ι → β) :=
  Pi.noZeroSMulDivisors _