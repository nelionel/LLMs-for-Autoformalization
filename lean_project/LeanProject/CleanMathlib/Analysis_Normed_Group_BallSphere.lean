import Mathlib.Analysis.Normed.Group.Uniform
open Metric Set Topology
variable {E : Type*} [i : SeminormedAddCommGroup E] {r : ℝ}
instance : InvolutiveNeg (sphere (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1
@[simp]
theorem coe_neg_sphere {r : ℝ} (v : sphere (0 : E) r) : ↑(-v) = (-v : E) :=
  rfl
instance : ContinuousNeg (sphere (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl
instance {r : ℝ} : InvolutiveNeg (ball (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1
@[simp] theorem coe_neg_ball {r : ℝ} (v : ball (0 : E) r) : ↑(-v) = (-v : E) := rfl
instance : ContinuousNeg (ball (0 : E) r) := IsInducing.subtypeVal.continuousNeg fun _ => rfl
instance {r : ℝ} : InvolutiveNeg (closedBall (0 : E) r) where
  neg := Subtype.map Neg.neg fun w => by simp
  neg_neg x := Subtype.ext <| neg_neg x.1
@[simp] theorem coe_neg_closedBall {r : ℝ} (v : closedBall (0 : E) r) : ↑(-v) = (-v : E) := rfl
instance : ContinuousNeg (closedBall (0 : E) r) := IsInducing.subtypeVal.continuousNeg  fun _ => rfl