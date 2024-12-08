import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.InvariantBasisNumber
variable (R : Type*) [CommRing R] [Nontrivial R]
instance (priority := 100) commRing_strongRankCondition : StrongRankCondition R :=
  inferInstance