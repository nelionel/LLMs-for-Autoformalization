import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.VonMangoldt
open scoped LSeries.notation
lemma ArithmeticFunction.one_eq_delta : ↗(1 : ArithmeticFunction ℂ) = δ := by
  ext
  simp only [one_apply, LSeries.delta]
section Moebius
namespace ArithmeticFunction
open LSeries Nat Complex
lemma not_LSeriesSummable_moebius_at_one : ¬ LSeriesSummable ↗μ 1 := by
  intro h
  refine not_summable_one_div_on_primes <| summable_ofReal.mp <| Summable.of_neg ?_
  simp only [← Pi.neg_def, Set.indicator_comp_of_zero ofReal_zero, ofReal_inv, ofReal_natCast]
  refine (h.indicator {n | n.Prime}).congr (fun n ↦ ?_)
  by_cases hn : n ∈ {p | p.Prime}
  · simp only [Pi.neg_apply, Set.indicator_of_mem hn, term_of_ne_zero hn.ne_zero,
      moebius_apply_prime hn, cpow_one, push_cast, neg_div]
  · simp only [one_div, Pi.neg_apply, Set.indicator_of_not_mem hn, ofReal_zero, neg_zero]
lemma LSeriesSummable_moebius_iff {s : ℂ} : LSeriesSummable ↗μ s ↔ 1 < s.re := by
  refine ⟨fun H ↦ ?_, LSeriesSummable_of_bounded_of_one_lt_re (m := 1) fun n _ ↦ ?_⟩
  · by_contra! h
    have h' : s.re ≤ (1 : ℂ).re := by simp only [one_re, h]
    exact not_LSeriesSummable_moebius_at_one <| LSeriesSummable.of_re_le_re h' H
  · rw [abs_intCast] 
    norm_cast
    exact abs_moebius_le_one
lemma abscissaOfAbsConv_moebius : abscissaOfAbsConv ↗μ = 1 := by
  simpa only [abscissaOfAbsConv, LSeriesSummable_moebius_iff, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _
end ArithmeticFunction
end Moebius
open Nat
open scoped ArithmeticFunction.zeta in
lemma ArithmeticFunction.const_one_eq_zeta {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) :
    (1 : ℕ → R) n = (ζ ·) n := by
  simp only [Pi.one_apply, zeta_apply, hn, ↓reduceIte, cast_one]
lemma LSeries.one_convolution_eq_zeta_convolution {R : Type*} [Semiring R] (f : ℕ → R) :
    (1 : ℕ → R) ⍟ f = ((ArithmeticFunction.zeta ·) : ℕ → R) ⍟ f :=
  convolution_congr ArithmeticFunction.const_one_eq_zeta fun _ ↦ rfl
lemma LSeries.convolution_one_eq_convolution_zeta {R : Type*} [Semiring R] (f : ℕ → R) :
    f ⍟ (1 : ℕ → R) = f ⍟ ((ArithmeticFunction.zeta ·) : ℕ → R) :=
  convolution_congr (fun _ ↦ rfl) ArithmeticFunction.const_one_eq_zeta
local notation (name := Dchar_one) "χ₁" => (1 : DirichletCharacter ℂ 1)
namespace DirichletCharacter
open ArithmeticFunction in
lemma isMultiplicative_toArithmeticFunction {N : ℕ} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) :
    (toArithmeticFunction (χ ·)).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m} {n} hm hn _ ↦ ?_⟩
  · simp only [toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, Nat.cast_one, map_one]
  · simp only [toArithmeticFunction, coe_mk, mul_eq_zero, hm, hn, false_or, Nat.cast_mul, map_mul,
      if_false]
lemma apply_eq_toArithmeticFunction_apply {N : ℕ} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R N) {n : ℕ} (hn : n ≠ 0) :
    χ n = toArithmeticFunction (χ ·) n := by
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, hn, ↓reduceIte]
open LSeries Nat Complex
lemma mul_convolution_distrib {R : Type*} [CommSemiring R] {n : ℕ} (χ : DirichletCharacter R n)
    (f g : ℕ → R) :
    (((χ ·) : ℕ → R) * f) ⍟ (((χ ·) : ℕ → R) * g) = ((χ ·) : ℕ → R) * (f ⍟ g) := by
  ext n
  simp only [Pi.mul_apply, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [(mem_divisorsAntidiagonal.mp hp).1.symm, cast_mul, map_mul]
  exact mul_mul_mul_comm ..
lemma mul_delta {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ * δ = δ :=
  LSeries.mul_delta <| by rw [cast_one, map_one]
lemma delta_mul {n : ℕ} (χ : DirichletCharacter ℂ n) : δ * ↗χ = δ :=
  mul_comm δ _ ▸ mul_delta ..
open ArithmeticFunction in
lemma convolution_mul_moebius {n : ℕ} (χ : DirichletCharacter ℂ n) : ↗χ ⍟ (↗χ * ↗μ) = δ := by
  have : (1 : ℕ → ℂ) ⍟ (μ ·) = δ := by
    rw [one_convolution_eq_zeta_convolution, ← one_eq_delta]
    simp_rw [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius]
  nth_rewrite 1 [← mul_one ↗χ]
  simpa only [mul_convolution_distrib χ 1 ↗μ, this] using mul_delta _
lemma modZero_eq_delta {χ : DirichletCharacter ℂ 0} : ↗χ = δ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [cast_zero, χ.map_nonunit not_isUnit_zero, delta, reduceCtorEq, if_false]
  rcases eq_or_ne n 1 with rfl | hn'
  · simp only [cast_one, map_one, delta, ↓reduceIte]
  have : ¬ IsUnit (n : ZMod 0) := fun h ↦ hn' <| ZMod.eq_one_of_isUnit_natCast h
  simp only [χ.map_nonunit this, delta, hn', ↓reduceIte]
lemma modOne_eq_one {R : Type*} [CommSemiring R] {χ : DirichletCharacter R 1} :
    ((χ ·) : ℕ → R) = 1 := by
  ext
  rw [χ.level_one, MulChar.one_apply (isUnit_of_subsingleton _), Pi.one_apply]
lemma LSeries_modOne_eq : L ↗χ₁ = L 1 :=
  congr_arg L modOne_eq_one
lemma not_LSeriesSummable_at_one {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    ¬ LSeriesSummable ↗χ 1 := by
  refine fun h ↦ (Real.not_summable_indicator_one_div_natCast hN 1) ?_
  refine h.norm.of_nonneg_of_le (fun m ↦ Set.indicator_apply_nonneg (fun _ ↦ by positivity))
    (fun n ↦ ?_)
  rw [norm_term_eq, one_re, Real.rpow_one, Set.indicator]
  split_ifs with h₁ h₂
  · rw [h₂, cast_zero, div_zero]
  · rw [h₁, χ.map_one, norm_one]
  all_goals positivity
lemma LSeriesSummable_of_one_lt_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗χ s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ ↦ χ.norm_le_one _) hs
lemma LSeriesSummable_iff {N : ℕ} (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ} :
    LSeriesSummable ↗χ s ↔ 1 < s.re := by
  refine ⟨fun H ↦ ?_, LSeriesSummable_of_one_lt_re χ⟩
  by_contra! h
  exact not_LSeriesSummable_at_one hN χ <| LSeriesSummable.of_re_le_re (by simp only [one_re, h]) H
lemma absicssaOfAbsConv_eq_one {N : ℕ} (hn : N ≠ 0) (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv ↗χ = 1 := by
  simpa only [abscissaOfAbsConv, LSeriesSummable_iff hn χ, ofReal_re, Set.Ioi_def,
    EReal.image_coe_Ioi, EReal.coe_one] using csInf_Ioo <| EReal.coe_lt_top _
lemma LSeriesSummable_mul {N : ℕ} (χ : DirichletCharacter ℂ N) {f : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable f s) :
    LSeriesSummable (↗χ * f) s := by
  refine .of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ norm_term_le s ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) <| norm_le_one ..
open scoped ArithmeticFunction.Moebius in
lemma LSeries.mul_mu_eq_one {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : L ↗χ s * L (↗χ * ↗μ) s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_of_one_lt_re χ hs) <|
          LSeriesSummable_mul χ <| ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs,
    convolution_mul_moebius, LSeries_delta, Pi.one_apply]
lemma LSeries_ne_zero_of_one_lt_re {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L ↗χ s ≠ 0 :=
  fun h ↦ by simpa only [h, zero_mul, zero_ne_one] using LSeries.mul_mu_eq_one χ hs
end DirichletCharacter
section zeta
open LSeries Nat Complex DirichletCharacter
lemma LSeries.abscissaOfAbsConv_one : abscissaOfAbsConv 1 = 1 :=
  modOne_eq_one (χ := χ₁) ▸ absicssaOfAbsConv_eq_one one_ne_zero χ₁
theorem LSeriesSummable_one_iff {s : ℂ} : LSeriesSummable 1 s ↔ 1 < s.re :=
  modOne_eq_one (χ := χ₁) ▸ LSeriesSummable_iff one_ne_zero χ₁
namespace ArithmeticFunction
lemma LSeries_zeta_eq : L ↗ζ = L 1 := by
  ext s
  exact (LSeries_congr s const_one_eq_zeta).symm
theorem LSeriesSummable_zeta_iff {s : ℂ} : LSeriesSummable (ζ ·) s ↔ 1 < s.re :=
  (LSeriesSummable_congr s const_one_eq_zeta).symm.trans <| LSeriesSummable_one_iff
@[deprecated (since := "2024-03-29")]
alias zeta_LSeriesSummable_iff_one_lt_re := LSeriesSummable_zeta_iff
lemma abscissaOfAbsConv_zeta : abscissaOfAbsConv ↗ζ = 1 := by
  rw [abscissaOfAbsConv_congr (g := 1) fun hn ↦ by simp [hn], abscissaOfAbsConv_one]
lemma LSeries_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L ↗ζ s = riemannZeta s := by
  simp only [LSeries, natCoe_apply, zeta_apply, cast_ite, cast_zero, cast_one,
    zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, cast_zero, zero_cpow (ne_zero_of_one_lt_re hs), div_zero]
  · simp only [term_of_ne_zero hn, hn, ↓reduceIte, one_div]
lemma LSeriesHasSum_zeta {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum ↗ζ s (riemannZeta s) :=
  LSeries_zeta_eq_riemannZeta hs ▸ (LSeriesSummable_zeta_iff.mpr hs).LSeriesHasSum
lemma LSeries_zeta_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1 := by
  rw [← LSeries_convolution' (LSeriesSummable_zeta_iff.mpr hs)
    (LSeriesSummable_moebius_iff.mpr hs)]
  simp only [← natCoe_apply, ← intCoe_apply, coe_mul, coe_zeta_mul_coe_moebius, one_eq_delta,
    LSeries_delta, Pi.one_apply]
lemma LSeries_zeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : L ↗ζ s ≠ 0 :=
  fun h ↦ by simpa only [h, zero_mul, zero_ne_one] using LSeries_zeta_mul_Lseries_moebius hs
end ArithmeticFunction
open ArithmeticFunction
lemma LSeries_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) : L 1 s = riemannZeta s :=
  LSeries_zeta_eq ▸ LSeries_zeta_eq_riemannZeta hs
lemma LSeriesHasSum_one {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum 1 s (riemannZeta s) :=
  LSeries_one_eq_riemannZeta hs ▸ (LSeriesSummable_one_iff.mpr hs).LSeriesHasSum
lemma LSeries_one_mul_Lseries_moebius {s : ℂ} (hs : 1 < s.re) : L 1 s * L ↗μ s = 1 :=
  LSeries_zeta_eq ▸ LSeries_zeta_mul_Lseries_moebius hs
lemma LSeries_one_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : L 1 s ≠ 0 :=
  LSeries_zeta_eq ▸ LSeries_zeta_ne_zero_of_one_lt_re hs
lemma riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  LSeries_one_eq_riemannZeta hs ▸ LSeries_one_ne_zero_of_one_lt_re hs
end zeta
section vonMangoldt
open LSeries Nat Complex ArithmeticFunction
namespace ArithmeticFunction
lemma convolution_vonMangoldt_zeta : ↗Λ ⍟ ↗ζ = ↗Complex.log := by
  ext n
  simpa only [zeta_apply, apply_ite, cast_zero, cast_one, LSeries.convolution_def, mul_zero,
    mul_one, mul_apply, natCoe_apply, ofReal_sum, ofReal_zero, log_apply, ofReal_log n.cast_nonneg]
    using congr_arg (ofReal <| · n) vonMangoldt_mul_zeta
lemma convolution_vonMangoldt_const_one : ↗Λ ⍟ 1 = ↗Complex.log :=
  (convolution_one_eq_convolution_zeta _).trans convolution_vonMangoldt_zeta
lemma LSeriesSummable_vonMangoldt {s : ℂ} (hs : 1 < s.re) : LSeriesSummable ↗Λ s := by
  have hf := LSeriesSummable_logMul_of_lt_re
    (show abscissaOfAbsConv 1 < s.re by rw [abscissaOfAbsConv_one]; exact_mod_cast hs)
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_term_le s ?_) hf
  have hΛ : ‖↗Λ n‖ ≤ ‖Complex.log n‖ := by
    simp only [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg vonMangoldt_nonneg,
      ← Complex.natCast_log, _root_.abs_of_nonneg <| Real.log_natCast_nonneg n]
    exact ArithmeticFunction.vonMangoldt_le_log
  exact hΛ.trans <| by simp only [norm_eq_abs, norm_mul, Pi.one_apply, norm_one, mul_one, le_refl]
end ArithmeticFunction
namespace DirichletCharacter
lemma convolution_twist_vonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (↗χ * ↗Λ) ⍟ ↗χ = ↗χ * ↗Complex.log := by
  rw [← convolution_vonMangoldt_const_one, ← χ.mul_convolution_distrib, mul_one]
lemma LSeriesSummable_twist_vonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (↗χ * ↗Λ) s :=
  LSeriesSummable_mul χ <| LSeriesSummable_vonMangoldt hs
lemma LSeries_twist_vonMangoldt_eq {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗Λ) s = - deriv (L ↗χ) s / L ↗χ s := by
  rcases eq_or_ne N 0 with rfl | hN
  · simpa only [modZero_eq_delta, delta_mul_eq_smul_delta, vonMangoldt_apply_one, ofReal_zero,
      zero_smul, LSeries_zero, Pi.zero_apply, LSeries_delta, Pi.one_apply, div_one, zero_eq_neg]
      using deriv_const s 1
  have hχ : LSeriesSummable ↗χ s := (LSeriesSummable_iff hN χ).mpr hs
  have hs' : abscissaOfAbsConv ↗χ < s.re := by
    rwa [absicssaOfAbsConv_eq_one hN, ← EReal.coe_one, EReal.coe_lt_coe_iff]
  have hΛ : LSeriesSummable (↗χ * ↗Λ) s := LSeriesSummable_twist_vonMangoldt χ hs
  rw [eq_div_iff <| LSeries_ne_zero_of_one_lt_re χ hs, ← LSeries_convolution' hΛ hχ,
    convolution_twist_vonMangoldt, LSeries_deriv hs', neg_neg]
  exact LSeries_congr s fun _ ↦ by simp only [Pi.mul_apply, mul_comm, logMul]
end DirichletCharacter
namespace ArithmeticFunction
open DirichletCharacter in
lemma LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) : L ↗Λ s = - deriv (L 1) s / L 1 s := by
  refine (LSeries_congr s fun {n} _ ↦ ?_).trans <|
    LSeries_modOne_eq ▸ LSeries_twist_vonMangoldt_eq χ₁ hs
  simp only [Subsingleton.eq_one (n : ZMod 1), map_one, Pi.mul_apply, one_mul]
lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = - deriv riemannZeta s / riemannZeta s := by
  suffices deriv (L 1) s = deriv riemannZeta s by
    rw [LSeries_vonMangoldt_eq hs, ← LSeries_one_eq_riemannZeta hs, this]
  refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
    fun _ ↦ LSeries_one_eq_riemannZeta⟩
end ArithmeticFunction
end vonMangoldt