import Mathlib.Algebra.GroupWithZero.Action.Opposite
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Opposite
assert_not_exists LinearMap
section
variable {R M : Type*} [Semiring R] [AddCommMonoid M]
instance (priority := 910) Semiring.toOppositeModule [Semiring R] : Module Rᵐᵒᵖ R :=
  { MonoidWithZero.toOppositeMulActionWithZero R with
    smul_add := fun _ _ _ => add_mul _ _ _
    add_smul := fun _ _ _ => mul_add _ _ _ }
end
namespace MulOpposite
universe u v
variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
instance instModule : Module R Mᵐᵒᵖ where
  add_smul _ _ _ := unop_injective <| add_smul _ _ _
  zero_smul _ := unop_injective <| zero_smul _ _
end MulOpposite