import Mathlib.Algebra.Group.AddChar
import Mathlib.MeasureTheory.MeasurableSpace.Defs
namespace AddChar
variable {A M : Type*} [AddMonoid A] [Monoid M] [MeasurableSpace A] [MeasurableSpace M]
@[nolint unusedArguments]
instance instMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] :
    MeasurableSpace (AddChar A M) :=
  ⊤
instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] :
    DiscreteMeasurableSpace (AddChar A M) :=
  ⟨fun _ ↦ trivial⟩
end AddChar