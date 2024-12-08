import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
instance : StarRing ℝ :=
  starRingOfComm
instance : TrivialStar ℝ :=
  ⟨fun _ => rfl⟩