import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.GroupWithZero.NeZero
assert_not_exists Equiv.Perm.equivUnitsEnd
assert_not_exists Prod.fst_mul
assert_not_exists Ring
open Function
variable {α : Type*}
instance CancelMonoidWithZero.faithfulSMul [CancelMonoidWithZero α] [Nontrivial α] :
    FaithfulSMul α α where eq_of_smul_eq_smul  h := mul_left_injective₀ one_ne_zero (h 1)