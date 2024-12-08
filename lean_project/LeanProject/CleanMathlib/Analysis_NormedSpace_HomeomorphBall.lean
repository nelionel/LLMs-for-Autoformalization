import Mathlib.Topology.PartialHomeomorph
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Data.Real.Sqrt
open Set Metric Pointwise
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable section
@[simps (config := .lemmasOnly)]
def PartialHomeomorph.univUnitBall : PartialHomeomorph E E where
  toFun x := (√(1 + ‖x‖ ^ 2))⁻¹ • x
  invFun y := (√(1 - ‖(y : E)‖ ^ 2))⁻¹ • (y : E)
  source := univ
  target := ball 0 1
  map_source' x _ := by
    have : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← _root_.div_eq_inv_mul,
      div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr this), ← abs_norm x, ← sq_lt_sq,
      abs_norm, Real.sq_sqrt this.le]
    exact lt_one_add _
  map_target' _ _ := trivial
  left_inv' x _ := by
    field_simp [norm_smul, smul_smul, (zero_lt_one_add_norm_sq x).ne', sq_abs,
      Real.sq_sqrt (zero_lt_one_add_norm_sq x).le, ← Real.sqrt_div (zero_lt_one_add_norm_sq x).le]
  right_inv' y hy := by
    have : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    field_simp [norm_smul, smul_smul, this.ne', sq_abs, Real.sq_sqrt this.le,
      ← Real.sqrt_div this.le]
  open_source := isOpen_univ
  open_target := isOpen_ball
  continuousOn_toFun := by
    suffices Continuous fun (x : E) => (√(1 + ‖x‖ ^ 2))⁻¹
     from (this.smul continuous_id).continuousOn
    refine Continuous.inv₀ ?_ fun x => Real.sqrt_ne_zero'.mpr (by positivity)
    continuity
  continuousOn_invFun := by
    have : ∀ y ∈ ball (0 : E) 1, √(1 - ‖(y : E)‖ ^ 2) ≠ 0 := fun y hy ↦ by
      rw [Real.sqrt_ne_zero']
      nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    exact ContinuousOn.smul (ContinuousOn.inv₀
      (continuousOn_const.sub (continuous_norm.continuousOn.pow _)).sqrt this) continuousOn_id
@[simp]
theorem PartialHomeomorph.univUnitBall_apply_zero : univUnitBall (0 : E) = 0 := by
  simp [PartialHomeomorph.univUnitBall_apply]
@[simp]
theorem PartialHomeomorph.univUnitBall_symm_apply_zero : univUnitBall.symm (0 : E) = 0 := by
  simp [PartialHomeomorph.univUnitBall_symm_apply]
@[simps! (config := .lemmasOnly)]
def Homeomorph.unitBall : E ≃ₜ ball (0 : E) 1 :=
  (Homeomorph.Set.univ _).symm.trans PartialHomeomorph.univUnitBall.toHomeomorphSourceTarget
@[simp]
theorem Homeomorph.coe_unitBall_apply_zero :
    (Homeomorph.unitBall (0 : E) : E) = 0 :=
  PartialHomeomorph.univUnitBall_apply_zero
variable {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]
namespace PartialHomeomorph
@[simps!]
def unitBallBall (c : P) (r : ℝ) (hr : 0 < r) : PartialHomeomorph E P :=
  ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toPartialHomeomorphOfImageEq
      (ball 0 1) isOpen_ball (ball c r) <| by
    change (IsometryEquiv.vaddConst c) ∘ (r • ·) '' ball (0 : E) 1 = ball c r
    rw [image_comp, image_smul, smul_unitBall hr.ne', IsometryEquiv.image_ball]
    simp [abs_of_pos hr]
def univBall (c : P) (r : ℝ) : PartialHomeomorph E P :=
  if h : 0 < r then univUnitBall.trans' (unitBallBall c r h) rfl
  else (IsometryEquiv.vaddConst c).toHomeomorph.toPartialHomeomorph
@[simp]
theorem univBall_source (c : P) (r : ℝ) : (univBall c r).source = univ := by
  unfold univBall; split_ifs <;> rfl
theorem univBall_target (c : P) {r : ℝ} (hr : 0 < r) : (univBall c r).target = ball c r := by
  rw [univBall, dif_pos hr]; rfl
theorem ball_subset_univBall_target (c : P) (r : ℝ) : ball c r ⊆ (univBall c r).target := by
  by_cases hr : 0 < r
  · rw [univBall_target c hr]
  · rw [univBall, dif_neg hr]
    exact subset_univ _
@[simp]
theorem univBall_apply_zero (c : P) (r : ℝ) : univBall c r 0 = c := by
  unfold univBall; split_ifs <;> simp
@[simp]
theorem univBall_symm_apply_center (c : P) (r : ℝ) : (univBall c r).symm c = 0 := by
  have : 0 ∈ (univBall c r).source := by simp
  simpa only [univBall_apply_zero] using (univBall c r).left_inv this
@[continuity]
theorem continuous_univBall (c : P) (r : ℝ) : Continuous (univBall c r) := by
  simpa [continuous_iff_continuousOn_univ] using (univBall c r).continuousOn
theorem continuousOn_univBall_symm (c : P) (r : ℝ) : ContinuousOn (univBall c r).symm (ball c r) :=
  (univBall c r).symm.continuousOn.mono <| ball_subset_univBall_target c r
end PartialHomeomorph