import Mathlib.Analysis.Complex.CauchyIntegral
#adaptation_note
namespace Complex
open Nat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
section ball
variable {c : ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball c r))
variable {z : ℂ} (hz : z ∈ Metric.ball c r)
include hf hz in
lemma hasSum_taylorSeries_on_ball :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : ∃ r' < r, 0 < r' ∧ z ∈ Metric.ball c r' := by
    obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    exact ⟨r', h₂, Metric.pos_of_mem_ball h₁, Metric.mem_ball'.mpr h₁⟩
  lift r' to NNReal using hr'₀.le
  have hz' : z - c ∈ EMetric.ball 0 r' := by
    rw [Metric.emetric_ball_nnreal]
    exact mem_ball_zero_iff.mpr hzr'
  have H := (hf.mono <| Metric.closedBall_subset_ball hr').hasFPowerSeriesOnBall hr'₀
      |>.hasSum_iteratedFDeriv hz'
  simp only [add_sub_cancel] at H
  convert H using 4 with n
  simpa only [iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul, mul_one, Finset.prod_const,
    Finset.card_fin]
    using ((iteratedFDeriv ℂ n f c).map_smul_univ (fun _ ↦ z - c) (fun _ ↦ 1)).symm
include hf hz in
lemma taylorSeries_eq_on_ball :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_ball hf hz).tsum_eq
include hz in
lemma taylorSeries_eq_on_ball' {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_on_ball hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]
end ball
section emetric
variable {c : ℂ} {r : ENNReal} (hf : DifferentiableOn ℂ f (EMetric.ball c r))
variable {z : ℂ} (hz : z ∈ EMetric.ball c r)
include hf hz in
lemma hasSum_taylorSeries_on_emetric_ball :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hzr', hr'⟩ := exists_between (EMetric.mem_ball'.mp hz)
  lift r' to NNReal using ne_top_of_lt hr'
  rw [← EMetric.mem_ball', Metric.emetric_ball_nnreal] at hzr'
  refine hasSum_taylorSeries_on_ball ?_ hzr'
  rw [← Metric.emetric_ball_nnreal]
  exact hf.mono <| EMetric.ball_subset_ball hr'.le
include hf hz in
lemma taylorSeries_eq_on_emetric_ball :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_emetric_ball hf hz).tsum_eq
include hz in
lemma taylorSeries_eq_on_emetric_ball' {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (EMetric.ball c r)) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_on_emetric_ball hf hz using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]
end emetric
section entire
variable {f : ℂ → E} (hf : Differentiable ℂ f) (c z : ℂ)
include hf in
lemma hasSum_taylorSeries_of_entire :
    HasSum (fun n : ℕ ↦ (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
  hasSum_taylorSeries_on_emetric_ball hf.differentiableOn <| EMetric.mem_ball.mpr <|
    edist_lt_top ..
include hf in
lemma taylorSeries_eq_of_entire :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_of_entire hf c z).tsum_eq
lemma taylorSeries_eq_of_entire' {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∑' n : ℕ, (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm, smul_eq_mul, smul_eq_mul, mul_assoc]
end entire
end Complex