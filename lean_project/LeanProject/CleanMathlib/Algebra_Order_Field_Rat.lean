import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.NNRat.Defs
namespace Rat
instance instLinearOrderedField : LinearOrderedField ℚ where
  __ := instLinearOrderedCommRing
  __ := instField
end Rat
deriving instance CanonicallyLinearOrderedSemifield, LinearOrderedSemifield,
  LinearOrderedCommGroupWithZero for NNRat