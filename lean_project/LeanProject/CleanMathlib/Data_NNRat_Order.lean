import Mathlib.Data.NNRat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Nonneg.Ring
deriving instance CanonicallyOrderedCommSemiring for NNRat
deriving instance CanonicallyLinearOrderedAddCommMonoid for NNRat
instance NNRat.instOrderedSub : OrderedSub ℚ≥0 := Nonneg.orderedSub