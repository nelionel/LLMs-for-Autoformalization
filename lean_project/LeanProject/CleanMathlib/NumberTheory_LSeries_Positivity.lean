import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Positivity
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Deriv
open scoped ComplexOrder
open Complex
namespace LSeries
lemma iteratedDeriv_alternating {a : ℕ → ℂ} (hn : 0 ≤ a) {x : ℝ}
    (h : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries a) x := by
  rw [LSeries_iteratedDeriv _ h, LSeries, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
    one_mul]
  refine tsum_nonneg fun k ↦ ?_
  rw [LSeries.term_def]
  split
  · exact le_rfl
  · refine mul_nonneg ?_ <| (inv_natCast_cpow_ofReal_pos (by assumption) x).le
    induction n with
    | zero => simpa only [Function.iterate_zero, id_eq] using hn k
    | succ n IH =>
        rw [Function.iterate_succ_apply']
        refine mul_nonneg ?_ IH
        simp only [← natCast_log, zero_le_real, Real.log_natCast_nonneg]
lemma positive {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {x : ℝ} (hx : abscissaOfAbsConv a < x) :
    0 < LSeries a x := by
  rw [LSeries]
  refine tsum_pos ?_ (fun n ↦ term_nonneg (ha₀ n) x) 1 <| term_pos one_ne_zero ha₁ x
  exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simpa only [ofReal_re] using hx
lemma positive_of_differentiable_of_eqOn {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℝ} (hx : abscissaOfAbsConv a ≤ x)
    (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : ℝ) :
    0 < f y := by
  have hxy : x < max x y + 1 := (le_max_left x y).trans_lt (lt_add_one _)
  have hxy' : abscissaOfAbsConv a < max x y + 1 := hx.trans_lt <| mod_cast hxy
  have hys : (max x y + 1 : ℂ) ∈ {s | x < s.re} := by
    simp only [Set.mem_setOf_eq, add_re, ofReal_re, one_re, hxy]
  have hfx : 0 < f (max x y + 1) := by
    simpa only [hf' hys, ofReal_add, ofReal_one] using positive ha₀ ha₁ hxy'
  refine (hfx.trans_le <| hf.apply_le_of_iteratedDeriv_alternating (fun n _ ↦ ?_) ?_)
  · have hs : IsOpen {s : ℂ | x < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    simpa only [hf'.iteratedDeriv_of_isOpen hs n hys, ofReal_add, ofReal_one] using
      iteratedDeriv_alternating ha₀ hxy' n
  · exact_mod_cast (le_max_right x y).trans (lt_add_one _).le
end LSeries
namespace ArithmeticFunction
lemma iteratedDeriv_LSeries_alternating (a : ArithmeticFunction ℂ) (hn : ∀ n, 0 ≤ a n) {x : ℝ}
    (h : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries (a ·)) x :=
  LSeries.iteratedDeriv_alternating hn h n
lemma LSeries_positive {a : ℕ → ℂ} (ha₀ : 0 ≤ a) (ha₁ : 0 < a 1) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) :
    0 < LSeries a x :=
  LSeries.positive ha₀ ha₁ hx
lemma LSeries_positive_of_differentiable_of_eqOn {a : ArithmeticFunction ℂ} (ha₀ : 0 ≤ (a ·))
    (ha₁ : 0 < a 1) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a ≤ x) (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : ℝ) :
    0 < f y :=
  LSeries.positive_of_differentiable_of_eqOn ha₀ ha₁ hf hx hf' y
end ArithmeticFunction