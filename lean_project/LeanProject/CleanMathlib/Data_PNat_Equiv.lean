import Mathlib.Data.PNat.Defs
import Mathlib.Logic.Equiv.Defs
@[simps (config := .asFn)]
def _root_.Equiv.pnatEquivNat : ℕ+ ≃ ℕ where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := PNat.succPNat_natPred
  right_inv := Nat.natPred_succPNat