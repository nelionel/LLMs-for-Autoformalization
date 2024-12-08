import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Convergence
open scoped LSeries.notation
open Complex LSeries
open Nat
def toArithmeticFunction {R : Type*} [Zero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else f n
  map_zero' := rfl
lemma toArithmeticFunction_congr {R : Type*} [Zero R] {f f' : ℕ → R}
    (h : ∀ {n}, n ≠ 0 → f n = f' n) :
    toArithmeticFunction f = toArithmeticFunction f' := by
  ext ⟨- | _⟩
  · simp only [zero_eq, ArithmeticFunction.map_zero]
  · simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, succ_ne_zero, ↓reduceIte,
      ne_eq, not_false_eq_true, h]
@[simp]
lemma ArithmeticFunction.toArithmeticFunction_eq_self {R : Type*} [Zero R]
    (f : ArithmeticFunction R) :
    toArithmeticFunction f = f := by
  ext n
  simp (config := {contextual := true}) [toArithmeticFunction, ArithmeticFunction.map_zero]
noncomputable def LSeries.convolution {R : Type*} [Semiring R] (f g : ℕ → R) : ℕ → R :=
  ⇑(toArithmeticFunction f * toArithmeticFunction g)
@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => LSeries.convolution
lemma LSeries.convolution_congr {R : Type*} [Semiring R] {f f' g g' : ℕ → R}
    (hf : ∀ {n}, n ≠ 0 → f n = f' n) (hg : ∀ {n}, n ≠ 0 → g n = g' n) :
    f ⍟ g = f' ⍟ g' := by
  simp only [convolution, toArithmeticFunction_congr hf, toArithmeticFunction_congr hg]
lemma ArithmeticFunction.coe_mul {R : Type*} [Semiring R] (f g : ArithmeticFunction R) :
    f ⍟ g = ⇑(f * g) := by
  simp only [convolution, ArithmeticFunction.toArithmeticFunction_eq_self]
namespace LSeries
lemma convolution_def {R : Type*} [Semiring R] (f g : ℕ → R) :
    f ⍟ g = fun n ↦ ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2 := by
  ext n
  simp only [convolution, toArithmeticFunction, ArithmeticFunction.mul_apply,
    ArithmeticFunction.coe_mk, mul_ite, mul_zero, ite_mul, zero_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  obtain ⟨h₁, h₂⟩ := ne_zero_of_mem_divisorsAntidiagonal hp
  simp only [h₂, ↓reduceIte, h₁]
@[simp]
lemma convolution_map_zero {R : Type*} [Semiring R] (f g : ℕ → R) : (f ⍟ g) 0 = 0 := by
  simp only [convolution_def, divisorsAntidiagonal_zero, Finset.sum_empty]
lemma term_convolution (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f ⍟ g) s n = ∑ p ∈ n.divisorsAntidiagonal, term f s p.1 * term g s p.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, divisorsAntidiagonal_zero, Finset.sum_empty]
  rw [term_of_ne_zero hn, convolution_def, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have ⟨hp₁, hp₂⟩ := ne_zero_of_mem_divisorsAntidiagonal hp
  rw [term_of_ne_zero hp₁ f s, term_of_ne_zero hp₂ g s, mul_comm_div, div_div, ← mul_div_assoc,
    ← natCast_mul_natCast_cpow, ← cast_mul, mul_comm p.2, (mem_divisorsAntidiagonal.mp hp).1]
open Set in
lemma term_convolution' (f g : ℕ → ℂ) (s : ℂ) :
    term (f ⍟ g) s = fun n ↦
      ∑' (b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n}), term f s b.val.1 * term g s b.val.2 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · 
    refine (term_zero ..).trans ?_
    have hS : (fun p ↦ p.1 * p.2) ⁻¹' {0} = {0} ×ˢ univ ∪ univ ×ˢ {0} := by
      ext
      simp only [mem_preimage, mem_singleton_iff, Nat.mul_eq_zero, mem_union, mem_prod, mem_univ,
        and_true, true_and]
    have : ∀ p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {0}, term f s p.val.1 * term g s p.val.2 = 0 := by
      rintro ⟨⟨p₁, p₂⟩, hp⟩
      rcases hS ▸ hp with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp only [term_zero, zero_mul, mul_zero]
    simp only [this, tsum_zero]
  rw [show (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
    Finset.tsum_subtype' n.divisorsAntidiagonal fun p ↦ term f s p.1 * term g s p.2,
    term_convolution f g s n]
end LSeries
open Set in
lemma LSeriesHasSum.convolution {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f ⍟ g) s (a * b) := by
  simp only [LSeriesHasSum, term_convolution']
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  exact (HasSum.mul hf hg hsum).tsum_fiberwise (fun p ↦ p.1 * p.2)
lemma LSeries_convolution' {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq
lemma LSeries_convolution {f g : ℕ → ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)
lemma LSeriesSummable.convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f ⍟ g) s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable
namespace ArithmeticFunction
lemma LSeriesHasSum_mul {f g : ArithmeticFunction ℂ} {s a b : ℂ} (hf : LSeriesHasSum ↗f s a)
    (hg : LSeriesHasSum ↗g s b) :
    LSeriesHasSum ↗(f * g) s (a * b) :=
  coe_mul f g ▸ hf.convolution hg
lemma LSeries_mul' {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution' hf hg
lemma LSeries_mul {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv ↗f < s.re) (hg : abscissaOfAbsConv ↗g < s.re) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution hf hg
lemma LSeriesSummable_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeriesSummable ↗(f * g) s :=
  coe_mul f g ▸ hf.convolution hg
end ArithmeticFunction