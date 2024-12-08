import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Prod
namespace Prod
variable {G H : Type*}
@[to_additive]
instance [OrderedCommGroup G] [OrderedCommGroup H] : OrderedCommGroup (G × H) :=
  { Prod.instCommGroup, Prod.instPartialOrder G H, Prod.instOrderedCancelCommMonoid
    with }
namespace Lex
@[to_additive]
instance orderedCommGroup [OrderedCommGroup G] [OrderedCommGroup H] :
    OrderedCommGroup (G ×ₗ H) where
  mul_le_mul_left _ _ := mul_le_mul_left'
@[to_additive]
instance linearOrderedCommGroup [LinearOrderedCommGroup G] [LinearOrderedCommGroup H] :
    LinearOrderedCommGroup (G ×ₗ H) where
  __ : LinearOrder (G ×ₗ H) := inferInstance
  mul_le_mul_left _ _ := mul_le_mul_left'
end Lex
end Prod