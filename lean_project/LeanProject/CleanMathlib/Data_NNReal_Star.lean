import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Star
assert_not_exists Finset
open scoped NNReal
instance : StarRing ℝ≥0 := starRingOfComm
instance : TrivialStar ℝ≥0 where
  star_trivial _ := rfl
instance : StarModule ℝ≥0 ℝ where
  star_smul := by simp only [star_trivial, eq_self_iff_true, forall_const]
instance {E : Type*} [AddCommMonoid E] [Star E] [Module ℝ E] [StarModule ℝ E] :
    StarModule ℝ≥0 E where
  star_smul _ := star_smul (_ : ℝ)