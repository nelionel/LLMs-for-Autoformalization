import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Order.Atoms
class IsSimpleRing (R : Type*) [NonUnitalNonAssocRing R] : Prop where
  simple : IsSimpleOrder (TwoSidedIdeal R)