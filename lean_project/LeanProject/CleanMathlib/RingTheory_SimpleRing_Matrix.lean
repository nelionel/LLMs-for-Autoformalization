import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.RingTheory.SimpleRing.Basic
namespace IsSimpleRing
variable (ι A : Type*) [Ring A] [Fintype ι] [Nonempty ι]
instance matrix [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A) where
  simple := TwoSidedIdeal.orderIsoMatricesOver (Nonempty.some ‹_›) (Nonempty.some ‹_›)
    |>.symm.isSimpleOrder
end IsSimpleRing