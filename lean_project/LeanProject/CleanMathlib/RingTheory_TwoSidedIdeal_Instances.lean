import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.NonUnitalSubring.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Basic
instance {R} [NonUnitalNonAssocRing R] : NonUnitalSubringClass (TwoSidedIdeal R) R where
  mul_mem _ hb := TwoSidedIdeal.mul_mem_left _ _ _ hb