import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Normed.Module.Ray
open Convex Pointwise Set Metric
class StrictConvexSpace (𝕜 E : Type*) [NormedLinearOrderedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] : Prop where
  strictConvex_closedBall : ∀ r : ℝ, 0 < r → StrictConvex 𝕜 (closedBall (0 : E) r)
variable (𝕜 : Type*) {E : Type*} [NormedLinearOrderedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
theorem strictConvex_closedBall [StrictConvexSpace 𝕜 E] (x : E) (r : ℝ) :
    StrictConvex 𝕜 (closedBall x r) := by
  rcases le_or_lt r 0 with hr | hr
  · exact (subsingleton_closedBall x hr).strictConvex
  rw [← vadd_closedBall_zero]
  exact (StrictConvexSpace.strictConvex_closedBall r hr).vadd _
variable [NormedSpace ℝ E]
theorem StrictConvexSpace.of_strictConvex_closed_unit_ball [LinearMap.CompatibleSMul E E 𝕜 ℝ]
    (h : StrictConvex 𝕜 (closedBall (0 : E) 1)) : StrictConvexSpace 𝕜 E :=
  ⟨fun r hr => by simpa only [smul_closedUnitBall_of_nonneg hr.le] using h.smul r⟩
theorem StrictConvexSpace.of_norm_combo_lt_one
    (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ∃ a b : ℝ, a + b = 1 ∧ ‖a • x + b • y‖ < 1) :
    StrictConvexSpace ℝ E := by
  refine
    StrictConvexSpace.of_strictConvex_closed_unit_ball ℝ
      ((convex_closedBall _ _).strictConvex' fun x hx y hy hne => ?_)
  rw [interior_closedBall (0 : E) one_ne_zero, closedBall_diff_ball,
    mem_sphere_zero_iff_norm] at hx hy
  rcases h x y hx hy hne with ⟨a, b, hab, hlt⟩
  use b
  rwa [AffineMap.lineMap_apply_module, interior_closedBall (0 : E) one_ne_zero, mem_ball_zero_iff,
    sub_eq_iff_eq_add.2 hab.symm]
theorem StrictConvexSpace.of_norm_combo_ne_one
    (h :
      ∀ x y : E,
        ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ ‖a • x + b • y‖ ≠ 1) :
    StrictConvexSpace ℝ E := by
  refine StrictConvexSpace.of_strictConvex_closed_unit_ball ℝ
    ((convex_closedBall _ _).strictConvex ?_)
  simp only [interior_closedBall _ one_ne_zero, closedBall_diff_ball, Set.Pairwise,
    frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
  intro x hx y hy hne
  rcases h x y hx hy hne with ⟨a, b, ha, hb, hab, hne'⟩
  exact ⟨_, ⟨a, b, ha, hb, hab, rfl⟩, mt mem_sphere_zero_iff_norm.1 hne'⟩
theorem StrictConvexSpace.of_norm_add_ne_two
    (h : ∀ ⦃x y : E⦄, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ‖x + y‖ ≠ 2) : StrictConvexSpace ℝ E := by
  refine
    StrictConvexSpace.of_norm_combo_ne_one fun x y hx hy hne =>
      ⟨1 / 2, 1 / 2, one_half_pos.le, one_half_pos.le, add_halves _, ?_⟩
  rw [← smul_add, norm_smul, Real.norm_of_nonneg one_half_pos.le, one_div, ← div_eq_inv_mul, Ne,
    div_eq_one_iff_eq (two_ne_zero' ℝ)]
  exact h hx hy hne
theorem StrictConvexSpace.of_pairwise_sphere_norm_ne_two
    (h : (sphere (0 : E) 1).Pairwise fun x y => ‖x + y‖ ≠ 2) : StrictConvexSpace ℝ E :=
  StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy =>
    h (mem_sphere_zero_iff_norm.2 hx) (mem_sphere_zero_iff_norm.2 hy)
theorem StrictConvexSpace.of_norm_add
    (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖x + y‖ = 2 → SameRay ℝ x y) : StrictConvexSpace ℝ E := by
  refine StrictConvexSpace.of_pairwise_sphere_norm_ne_two fun x hx y hy => mt fun h₂ => ?_
  rw [mem_sphere_zero_iff_norm] at hx hy
  exact (sameRay_iff_of_norm_eq (hx.trans hy.symm)).1 (h x y hx hy h₂)
variable [StrictConvexSpace ℝ E] {x y z : E} {a b r : ℝ}
theorem combo_mem_ball_of_ne (hx : x ∈ closedBall z r) (hy : y ∈ closedBall z r) (hne : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a • x + b • y ∈ ball z r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, mem_singleton_iff] at hx hy
    exact (hne (hx.trans hy.symm)).elim
  · simp only [← interior_closedBall _ hr] at hx hy ⊢
    exact strictConvex_closedBall ℝ z r hx hy hne ha hb hab
theorem openSegment_subset_ball_of_ne (hx : x ∈ closedBall z r) (hy : y ∈ closedBall z r)
    (hne : x ≠ y) : openSegment ℝ x y ⊆ ball z r :=
  (openSegment_subset_iff _).2 fun _ _ => combo_mem_ball_of_ne hx hy hne
theorem norm_combo_lt_of_ne (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hne : x ≠ y) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) : ‖a • x + b • y‖ < r := by
  simp only [← mem_ball_zero_iff, ← mem_closedBall_zero_iff] at hx hy ⊢
  exact combo_mem_ball_of_ne hx hy hne ha hb hab
theorem norm_add_lt_of_not_sameRay (h : ¬SameRay ℝ x y) : ‖x + y‖ < ‖x‖ + ‖y‖ := by
  simp only [sameRay_iff_inv_norm_smul_eq, not_or, ← Ne.eq_def] at h
  rcases h with ⟨hx, hy, hne⟩
  rw [← norm_pos_iff] at hx hy
  have hxy : 0 < ‖x‖ + ‖y‖ := add_pos hx hy
  have :=
    combo_mem_ball_of_ne (inv_norm_smul_mem_closed_unit_ball x)
      (inv_norm_smul_mem_closed_unit_ball y) hne (div_pos hx hxy) (div_pos hy hxy)
      (by rw [← add_div, div_self hxy.ne'])
  rwa [mem_ball_zero_iff, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, smul_inv_smul₀ hx.ne',
    smul_inv_smul₀ hy.ne', ← smul_add, norm_smul, Real.norm_of_nonneg (inv_pos.2 hxy).le, ←
    div_eq_inv_mul, div_lt_one hxy] at this
theorem lt_norm_sub_of_not_sameRay (h : ¬SameRay ℝ x y) : ‖x‖ - ‖y‖ < ‖x - y‖ := by
  nth_rw 1 [← sub_add_cancel x y] at h ⊢
  exact sub_lt_iff_lt_add.2 (norm_add_lt_of_not_sameRay fun H' => h <| H'.add_left SameRay.rfl)
theorem abs_lt_norm_sub_of_not_sameRay (h : ¬SameRay ℝ x y) : |‖x‖ - ‖y‖| < ‖x - y‖ := by
  refine abs_sub_lt_iff.2 ⟨lt_norm_sub_of_not_sameRay h, ?_⟩
  rw [norm_sub_rev]
  exact lt_norm_sub_of_not_sameRay (mt SameRay.symm h)
theorem sameRay_iff_norm_add : SameRay ℝ x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖ :=
  ⟨SameRay.norm_add, fun h => Classical.not_not.1 fun h' => (norm_add_lt_of_not_sameRay h').ne h⟩
theorem eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y :=
  (sameRay_iff_norm_add.mpr h₂).eq_of_norm_eq h₁
theorem not_sameRay_iff_norm_add_lt : ¬SameRay ℝ x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖ :=
  sameRay_iff_norm_add.not.trans (norm_add_le _ _).lt_iff_ne.symm
theorem sameRay_iff_norm_sub : SameRay ℝ x y ↔ ‖x - y‖ = |‖x‖ - ‖y‖| :=
  ⟨SameRay.norm_sub, fun h =>
    Classical.not_not.1 fun h' => (abs_lt_norm_sub_of_not_sameRay h').ne' h⟩
theorem not_sameRay_iff_abs_lt_norm_sub : ¬SameRay ℝ x y ↔ |‖x‖ - ‖y‖| < ‖x - y‖ :=
  sameRay_iff_norm_sub.not.trans <| ne_comm.trans (abs_norm_sub_norm_le _ _).lt_iff_ne.symm
theorem norm_midpoint_lt_iff (h : ‖x‖ = ‖y‖) : ‖(1 / 2 : ℝ) • (x + y)‖ < ‖x‖ ↔ x ≠ y := by
  rw [norm_smul, Real.norm_of_nonneg (one_div_nonneg.2 zero_le_two), ← inv_eq_one_div, ←
    div_eq_inv_mul, div_lt_iff₀ (zero_lt_two' ℝ), mul_two, ← not_sameRay_iff_of_norm_eq h,
    not_sameRay_iff_norm_add_lt, h]