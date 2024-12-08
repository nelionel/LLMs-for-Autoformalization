import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
open Set Real Complex Filter Topology
namespace HurwitzZeta
noncomputable def hurwitzZeta (a : UnitAddCircle) (s : ℂ) :=
  hurwitzZetaEven a s + hurwitzZetaOdd a s
lemma hurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaEven a s = (hurwitzZeta a s + hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf
lemma hurwitzZetaOdd_eq (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaOdd a s = (hurwitzZeta a s - hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf
lemma differentiableAt_hurwitzZeta (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (hurwitzZeta a) s :=
  (differentiableAt_hurwitzZetaEven a hs).add (differentiable_hurwitzZetaOdd a s)
lemma hasSum_hurwitzZeta_of_one_lt_re {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ 1 / (n + a : ℂ) ^ s) (hurwitzZeta a s) := by
  convert (hasSum_nat_hurwitzZetaEven_of_mem_Icc ha hs).add
      (hasSum_nat_hurwitzZetaOdd_of_mem_Icc ha hs) using 1
  ext1 n
  apply show ∀ (x y : ℂ), x = (x + y) / 2 + (x - y) / 2 by intros; ring
lemma hurwitzZeta_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * hurwitzZeta a s) (𝓝[≠] 1) (𝓝 1) := by
  simp only [hurwitzZeta, mul_add, (by simp : 𝓝 (1 : ℂ) = 𝓝 (1 + (1 - 1) * hurwitzZetaOdd a 1))]
  refine (hurwitzZetaEven_residue_one a).add ((Tendsto.mul ?_ ?_).mono_left nhdsWithin_le_nhds)
  exacts [tendsto_id.sub_const _, (differentiable_hurwitzZetaOdd a).continuous.tendsto _]
lemma differentiableAt_hurwitzZeta_sub_one_div (a : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s) 1 := by
  simp only [hurwitzZeta, add_sub_right_comm]
  exact (differentiableAt_hurwitzZetaEven_sub_one_div a).add (differentiable_hurwitzZetaOdd a 1)
lemma tendsto_hurwitzZeta_sub_one_div_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s) (𝓝 1) (𝓝 (hurwitzZeta a 1)) := by
  simp only [hurwitzZeta, add_sub_right_comm]
  refine (tendsto_hurwitzZetaEven_sub_one_div_nhds_one a).add ?_
  exact (differentiable_hurwitzZetaOdd a 1).continuousAt.tendsto
lemma differentiable_hurwitzZeta_sub_hurwitzZeta (a b : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZeta a s - hurwitzZeta b s) := by
  simp only [hurwitzZeta, add_sub_add_comm]
  refine (differentiable_hurwitzZetaEven_sub_hurwitzZetaEven a b).add (Differentiable.sub ?_ ?_)
  all_goals apply differentiable_hurwitzZetaOdd
noncomputable def expZeta (a : UnitAddCircle) (s : ℂ) :=
  cosZeta a s + I * sinZeta a s
lemma cosZeta_eq (a : UnitAddCircle) (s : ℂ) :
    cosZeta a s = (expZeta a s + expZeta (-a) s) / 2 := by
  rw [expZeta, expZeta, cosZeta_neg, sinZeta_neg]
  ring_nf
lemma sinZeta_eq (a : UnitAddCircle) (s : ℂ) :
    sinZeta a s = (expZeta a s - expZeta (-a) s) / (2 * I) := by
  rw [expZeta, expZeta, cosZeta_neg, sinZeta_neg]
  field_simp
  ring_nf
lemma hasSum_expZeta_of_one_lt_re (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ cexp (2 * π * I * a * n) / n ^ s) (expZeta a s) := by
  convert (hasSum_nat_cosZeta a hs).add ((hasSum_nat_sinZeta a hs).mul_left I) using 1
  ext1 n
  simp only [mul_right_comm _ I, ← cos_add_sin_I, push_cast]
  rw [add_div, mul_div, mul_comm _ I]
lemma differentiableAt_expZeta (a : UnitAddCircle) (s : ℂ) (hs : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (expZeta a) s := by
  apply DifferentiableAt.add
  · exact differentiableAt_cosZeta a hs
  · apply (differentiableAt_const _).mul (differentiableAt_sinZeta a s)
lemma differentiable_expZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
    Differentiable ℂ (expZeta a) :=
  (differentiableAt_expZeta a · (Or.inr ha))
lemma LSeriesHasSum_exp (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (cexp <| 2 * π * I * a * ·) s (expZeta a s) :=
  (hasSum_expZeta_of_one_lt_re a hs).congr_fun
    (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)
lemma hurwitzZeta_one_sub (a : UnitAddCircle) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : a ≠ 0 ∨ s ≠ 1) :
    hurwitzZeta a (1 - s) = (2 * π) ^ (-s) * Gamma s *
    (exp (-π * I * s / 2) * expZeta a s + exp (π * I * s / 2) * expZeta (-a) s) := by
  rw [hurwitzZeta, hurwitzZetaEven_one_sub a hs hs', hurwitzZetaOdd_one_sub a hs,
    expZeta, expZeta, Complex.cos, Complex.sin, sinZeta_neg, cosZeta_neg]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring,
    show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  generalize (2 * π : ℂ) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf
lemma expZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ 1 - n) :
    expZeta a (1 - s) = (2 * π) ^ (-s) * Gamma s *
    (exp (π * I * s / 2) * hurwitzZeta a s + exp (-π * I * s / 2) * hurwitzZeta (-a) s) := by
  have hs' (n : ℕ) : s ≠ -↑n := by
    convert hs (n + 1) using 1
    push_cast
    ring
  rw [expZeta, cosZeta_one_sub a hs, sinZeta_one_sub a hs', hurwitzZeta, hurwitzZeta,
    hurwitzZetaEven_neg, hurwitzZetaOdd_neg, Complex.cos, Complex.sin]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring,
    show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  generalize (2 * π : ℂ) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf
  rw [I_sq]
  ring_nf
end HurwitzZeta