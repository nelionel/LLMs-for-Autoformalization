import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace CStarAlgebra
section SpanNonneg
open Submodule
lemma span_nonneg_inter_closedBall {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg, span_le]
  intro x hx
  obtain (rfl | hx_pos) := eq_zero_or_norm_pos x
  · exact zero_mem _
  · suffices (r * ‖x‖⁻¹ : ℂ)⁻¹ • ((r * ‖x‖⁻¹ : ℂ) • x) = x by
      rw [← this]
      refine smul_mem _ _ (subset_span <| Set.mem_inter ?_ ?_)
      · norm_cast
        exact smul_nonneg (by positivity) hx
      · simp [mul_smul, norm_smul, abs_of_pos hr, inv_mul_cancel₀ hx_pos.ne']
    apply inv_smul_smul₀
    norm_cast
    positivity
lemma span_nonneg_inter_ball {r : ℝ} (hr : 0 < r) :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 r) = ⊤ := by
  rw [eq_top_iff, ← span_nonneg_inter_closedBall (half_pos hr)]
  gcongr
  exact Metric.closedBall_subset_ball <| half_lt_self hr
lemma span_nonneg_inter_unitClosedBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.closedBall 0 1) = ⊤ :=
  span_nonneg_inter_closedBall zero_lt_one
lemma span_nonneg_inter_unitBall :
    span ℂ ({x : A | 0 ≤ x} ∩ Metric.ball 0 1) = ⊤ :=
  span_nonneg_inter_ball zero_lt_one
end SpanNonneg
end CStarAlgebra