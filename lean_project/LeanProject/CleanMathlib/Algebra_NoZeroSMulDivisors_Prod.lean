import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Group.Action.Prod
variable {R M N : Type*}
namespace Prod
instance noZeroSMulDivisors [Zero R] [Zero M] [Zero N]
    [SMulWithZero R M] [SMulWithZero R N] [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] :
    NoZeroSMulDivisors R (M × N) :=
  { eq_zero_or_eq_zero_of_smul_eq_zero := by 
      intro c ⟨x, y⟩ h
      exact or_iff_not_imp_left.mpr fun hc =>
        mk.inj_iff.mpr
          ⟨(smul_eq_zero.mp (congr_arg fst h)).resolve_left hc,
            (smul_eq_zero.mp (congr_arg snd h)).resolve_left hc⟩ }
end Prod