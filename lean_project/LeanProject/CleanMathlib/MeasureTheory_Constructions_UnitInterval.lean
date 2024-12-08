import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped unitInterval
open MeasureTheory
namespace unitInterval
noncomputable instance : MeasureSpace I := Measure.Subtype.measureSpace
theorem volume_def : (volume : Measure I) = volume.comap Subtype.val := rfl
instance : IsProbabilityMeasure (volume : Measure I) where
  measure_univ := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one]
@[measurability]
theorem measurable_symm : Measurable symm := continuous_symm.measurable
end unitInterval