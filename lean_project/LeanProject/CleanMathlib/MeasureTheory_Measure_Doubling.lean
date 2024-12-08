import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace ENNReal NNReal Topology
class IsUnifLocDoublingMeasure {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  (μ : Measure α) : Prop where
  exists_measure_closedBall_le_mul'' :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε)
namespace IsUnifLocDoublingMeasure
variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]
theorem exists_measure_closedBall_le_mul :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε) :=
  exists_measure_closedBall_le_mul''
def doublingConstant : ℝ≥0 :=
  Classical.choose <| exists_measure_closedBall_le_mul μ
theorem exists_measure_closedBall_le_mul' :
    ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ doublingConstant μ * μ (closedBall x ε) :=
  Classical.choose_spec <| exists_measure_closedBall_le_mul μ
theorem exists_eventually_forall_measure_closedBall_le_mul (K : ℝ) :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, ∀ t ≤ K, μ (closedBall x (t * ε)) ≤ C * μ (closedBall x ε) := by
  let C := doublingConstant μ
  have hμ :
    ∀ n : ℕ, ∀ᶠ ε in 𝓝[>] 0, ∀ x,
      μ (closedBall x ((2 : ℝ) ^ n * ε)) ≤ ↑(C ^ n) * μ (closedBall x ε) := by
    intro n
    induction' n with n ih
    · simp
    replace ih := eventually_nhdsWithin_pos_mul_left (two_pos : 0 < (2 : ℝ)) ih
    refine (ih.and (exists_measure_closedBall_le_mul' μ)).mono fun ε hε x => ?_
    calc
      μ (closedBall x ((2 : ℝ) ^ (n + 1) * ε)) = μ (closedBall x ((2 : ℝ) ^ n * (2 * ε))) := by
        rw [pow_succ, mul_assoc]
      _ ≤ ↑(C ^ n) * μ (closedBall x (2 * ε)) := hε.1 x
      _ ≤ ↑(C ^ n) * (C * μ (closedBall x ε)) := by gcongr; exact hε.2 x
      _ = ↑(C ^ (n + 1)) * μ (closedBall x ε) := by rw [← mul_assoc, pow_succ, ENNReal.coe_mul]
  rcases lt_or_le K 1 with (hK | hK)
  · refine ⟨1, ?_⟩
    simp only [ENNReal.coe_one, one_mul]
    refine eventually_mem_nhdsWithin.mono fun ε hε x t ht ↦ ?_
    gcongr
    nlinarith [mem_Ioi.mp hε]
  · use C ^ ⌈Real.logb 2 K⌉₊
    filter_upwards [hμ ⌈Real.logb 2 K⌉₊, eventually_mem_nhdsWithin] with ε hε hε₀ x t ht
    refine le_trans ?_ (hε x)
    gcongr
    · exact (mem_Ioi.mp hε₀).le
    · refine ht.trans ?_
      rw [← Real.rpow_natCast, ← Real.logb_le_iff_le_rpow]
      exacts [Nat.le_ceil _, by norm_num, by linarith]
def scalingConstantOf (K : ℝ) : ℝ≥0 :=
  max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1
@[simp]
theorem one_le_scalingConstantOf (K : ℝ) : 1 ≤ scalingConstantOf μ K :=
  le_max_of_le_right <| le_refl 1
theorem eventually_measure_mul_le_scalingConstantOf_mul (K : ℝ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ x t r, t ∈ Ioc 0 K → r ≤ R →
          μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) := by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closedBall_le_mul μ K)
  rcases mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine ⟨R, Rpos, fun x t r ht hr => ?_⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg ht.1 rneg
    simp only [closedBall_eq_empty.2 this, measure_empty, zero_le']
  · simp only [mul_zero, closedBall_zero]
    refine le_mul_of_one_le_of_le ?_ le_rfl
    apply ENNReal.one_le_coe_iff.2 (le_max_right _ _)
  · apply (hR ⟨rpos, hr⟩ x t ht.2).trans
    gcongr
    apply le_max_left
theorem eventually_measure_le_scaling_constant_mul (K : ℝ) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x, μ (closedBall x (K * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) := by
  filter_upwards [Classical.choose_spec
      (exists_eventually_forall_measure_closedBall_le_mul μ K)] with r hr x
  exact (hr x K le_rfl).trans (mul_le_mul_right' (ENNReal.coe_le_coe.2 (le_max_left _ _)) _)
theorem eventually_measure_le_scaling_constant_mul' (K : ℝ) (hK : 0 < K) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x,
      μ (closedBall x r) ≤ scalingConstantOf μ K⁻¹ * μ (closedBall x (K * r)) := by
  convert eventually_nhdsWithin_pos_mul_left hK (eventually_measure_le_scaling_constant_mul μ K⁻¹)
  simp [inv_mul_cancel_left₀ hK.ne']
def scalingScaleOf (K : ℝ) : ℝ :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose
theorem scalingScaleOf_pos (K : ℝ) : 0 < scalingScaleOf μ K :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.1
theorem measure_mul_le_scalingConstantOf_mul {K : ℝ} {x : α} {t r : ℝ} (ht : t ∈ Ioc 0 K)
    (hr : r ≤ scalingScaleOf μ K) :
    μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.2 x t r ht hr
end IsUnifLocDoublingMeasure