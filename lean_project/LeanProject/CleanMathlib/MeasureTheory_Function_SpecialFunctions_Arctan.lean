import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
namespace Real
@[measurability]
theorem measurable_arctan : Measurable arctan :=
  continuous_arctan.measurable
end Real
section RealComposition
open Real
variable {α : Type*} {m : MeasurableSpace α} {f : α → ℝ}
@[measurability]
theorem Measurable.arctan (hf : Measurable f) : Measurable fun x => arctan (f x) :=
  measurable_arctan.comp hf
end RealComposition