import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Defs
class IsLocalRing (R : Type*) [Semiring R] extends Nontrivial R : Prop where
  of_is_unit_or_is_unit_of_add_one ::
  isUnit_or_isUnit_of_add_one {a b : R} (h : a + b = 1) : IsUnit a ∨ IsUnit b
@[deprecated (since := "2024-11-09")] alias LocalRing := IsLocalRing