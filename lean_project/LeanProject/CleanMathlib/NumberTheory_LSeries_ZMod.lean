import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.NumberTheory.LSeries.RiemannZeta
open HurwitzZeta Complex ZMod Finset Classical Topology Filter Set
open scoped Real
namespace ZMod
variable {N : ℕ} [NeZero N]
lemma LSeriesSummable_of_one_lt_re (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LSeriesSummable (Φ ·) s := by
  let c := max' _ <| univ_nonempty.image (Complex.abs ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)
noncomputable def LFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s
lemma LFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) :
    LFunction Φ s = Φ 0 * riemannZeta s := by
  simp only [LFunction, Nat.cast_one, one_cpow, ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
    map_zero, hurwitzZeta_zero, one_mul]
lemma LFunction_eq_LSeries (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LFunction Φ s = LSeries (Φ ·) s := by
  rw [LFunction, LSeries, mul_sum, Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  congr 1 with j
  have : (j.val / N : ℝ) ∈ Set.Icc 0 1 := mem_Icc.mpr ⟨by positivity,
    (div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr <| Nat.cast_le.mpr (val_lt j).le⟩
  rw [toAddCircle_apply, ← (hasSum_hurwitzZeta_of_one_lt_re this hs).tsum_eq, ← mul_assoc,
    ← tsum_mul_left]
  congr 1 with m
  calc N ^ (-s) * Φ j * (1 / (m + (j.val / N : ℝ)) ^ s)
  _ = Φ j * (N ^ (-s) * (1 / (m + (j.val / N : ℝ)) ^ s)) := by
    rw [← mul_assoc, mul_comm _ (Φ _)]
  _ = Φ j * (1 / (N : ℝ) ^ s * (1 / ((j.val + N * m) / N : ℝ) ^ s)) := by
    simp only [cpow_neg, ← one_div, ofReal_div, ofReal_natCast, add_comm, add_div, ofReal_add,
      ofReal_mul, mul_div_cancel_left₀ (m : ℂ) (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ j / ((N : ℝ) * ((j.val + N * m) / N : ℝ)) ^ s := by 
    rw [one_div_mul_one_div, mul_one_div, mul_cpow_ofReal_nonneg] <;> positivity
  _ = Φ j / (N * (j.val + N * m) / N) ^ s := by
    simp only [ofReal_natCast, ofReal_div, ofReal_add, ofReal_mul, mul_div_assoc]
  _ = Φ j / (j.val + N * m) ^ s := by
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ ↑(j.val + N * m) / (↑(j.val + N * m)) ^ s := by
    simp only [Nat.cast_add, Nat.cast_mul, natCast_zmod_val, natCast_self, zero_mul, add_zero]
  _ = LSeries.term (Φ ·) s (j.val + N * m) := by
    rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]
lemma differentiableAt_LFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (LFunction Φ) s := by
  refine .mul (by fun_prop) ?_
  rcases ne_or_eq s 1 with hs' | rfl
  · exact .sum fun j _ ↦ (differentiableAt_hurwitzZeta _ hs').const_mul _
  · have := DifferentiableAt.sum (u := univ) fun j _ ↦
      (differentiableAt_hurwitzZeta_sub_one_div (toAddCircle j)).const_mul (Φ j)
    simpa only [mul_sub, sum_sub_distrib, ← sum_mul, hs.neg_resolve_left rfl, zero_mul, sub_zero]
lemma differentiable_LFunction_of_sum_zero {Φ : ZMod N → ℂ} (hΦ : ∑ j, Φ j = 0) :
    Differentiable ℂ (LFunction Φ) :=
  fun s ↦ differentiableAt_LFunction Φ s (Or.inr hΦ)
lemma LFunction_residue_one (Φ : ZMod N → ℂ) :
    Tendsto (fun s ↦ (s - 1) * LFunction Φ s) (𝓝[≠] 1) (𝓝 (∑ j, Φ j / N)) := by
  simp only [sum_div, LFunction, mul_sum]
  refine tendsto_finset_sum _ fun j _ ↦ ?_
  rw [(by ring : Φ j / N = Φ j * (1 / N * 1)), one_div, ← cpow_neg_one]
  simp only [show ∀ a b c d : ℂ, a * (b * (c * d)) = c * (b * (a * d)) by intros; ring]
  refine tendsto_const_nhds.mul (.mul ?_ <| hurwitzZeta_residue_one _)
  exact ((continuous_neg.const_cpow (Or.inl <| NeZero.ne _)).tendsto _).mono_left
    nhdsWithin_le_nhds
local notation "𝕖" => stdAddChar
private lemma LFunction_stdAddChar_eq_expZeta_of_one_lt_re (j : ZMod N) {s : ℂ} (hs : 1 < s.re) :
    LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  rw [toAddCircle_apply, ← (hasSum_expZeta_of_one_lt_re (j.val / N) hs).tsum_eq,
    LFunction_eq_LSeries _ hs, LSeries]
  congr 1 with n
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), ofReal_div, ofReal_natCast,
    ofReal_natCast, mul_assoc, div_mul_eq_mul_div, stdAddChar_apply]
  have := ZMod.toCircle_intCast (N := N) (j.val * n)
  conv_rhs at this => rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_assoc]
  rw [← this, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_zmod_val]
lemma LFunction_stdAddChar_eq_expZeta (j : ZMod N) (s : ℂ) (hjs : j ≠ 0 ∨ s ≠ 1) :
    LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  let U := if j = 0 then {z : ℂ | z ≠ 1} else univ 
  let V := {z : ℂ | 1 < re z} 
  have hUo : IsOpen U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using isOpen_compl_singleton
    · simp only [h, ↓reduceIte, isOpen_univ, U]
  let f := LFunction (fun k ↦ stdAddChar (j * k))
  let g := expZeta (toAddCircle j)
  have hU {u} : u ∈ U ↔ u ≠ 1 ∨ j ≠ 0 := by simp only [mem_ite_univ_right, U]; tauto
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu ↦ ?_) hUo
    refine (differentiableAt_LFunction _ _ ((hU.mp hu).imp_right fun h ↦ ?_)).differentiableWithinAt
    simp only [mul_comm j, AddChar.sum_mulShift _ (isPrimitive_stdAddChar _), h,
      ↓reduceIte, CharP.cast_eq_zero, or_true]
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu ↦ ?_) hUo
    refine (differentiableAt_expZeta _ _ ((hU.mp hu).imp_right fun h ↦ ?_)).differentiableWithinAt
    rwa [ne_eq, toAddCircle_eq_zero]
  have hUc : IsPreconnected U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using
        (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
    · simpa only [h, ↓reduceIte, U] using isPreconnected_univ
  have hV : V ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hUmem : 2 ∈ U := by simp [U]
  have hUmem' : s ∈ U := hU.mpr hjs.symm
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hUmem ?_ hUmem'
  filter_upwards [hV] with z using LFunction_stdAddChar_eq_expZeta_of_one_lt_re _
lemma LFunction_dft (Φ : ZMod N → ℂ) {s : ℂ} (hs : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s := by
  have (j : ZMod N) : Φ j * LFunction (fun k ↦ 𝕖 (-j * k)) s =
      Φ j * expZeta (toAddCircle (-j)) s := by
    by_cases h : -j ≠ 0 ∨ s ≠ 1
    · rw [LFunction_stdAddChar_eq_expZeta _ _ h]
    · simp only [neg_ne_zero, not_or, not_not] at h
      rw [h.1, show Φ 0 = 0 by tauto, zero_mul, zero_mul]
  simp only [LFunction, ← this, mul_sum]
  rw [dft_def, sum_comm]
  simp only [sum_mul, mul_sum, Circle.smul_def, smul_eq_mul, stdAddChar_apply, ← mul_assoc]
  congr 1 with j
  congr 1 with k
  rw [mul_assoc (Φ _), mul_comm (Φ _), neg_mul]
theorem LFunction_one_sub (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction Φ (1 - s) = N ^ (s - 1) * (2 * π) ^ (-s) * Gamma s *
      (cexp (π * I * s / 2) * LFunction (𝓕 Φ) s
       + cexp (-π * I * s / 2) * LFunction (𝓕 fun x ↦ Φ (-x)) s) := by
  rw [LFunction]
  have (j : ZMod N) :  Φ j * hurwitzZeta (toAddCircle j) (1 - s) = Φ j *
      ((2 * π) ^ (-s) * Gamma s * (cexp (-π * I * s / 2) *
      expZeta (toAddCircle j) s + cexp (π * I * s / 2) * expZeta (-toAddCircle j) s)) := by
    rcases eq_or_ne j 0 with rfl | hj
    · rcases hs' with hΦ | hs'
      · simp only [hΦ, zero_mul]
      · rw [hurwitzZeta_one_sub _ hs (Or.inr hs')]
    · rw [hurwitzZeta_one_sub _ hs (Or.inl <| toAddCircle_eq_zero.not.mpr hj)]
  simp only [this, mul_assoc _ _ (Gamma s)]
  generalize (2 * π) ^ (-s) * Gamma s = C
  simp_rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc,
    neg_sub]
  congr 2
  rw [LFunction_dft _ hs', LFunction_dft _ (hs'.imp_left <| by simp only [neg_zero, imp_self])]
  conv_rhs => enter [2, 2]; rw [← (Equiv.neg _).sum_comp _ _ (by simp), Equiv.neg_apply]
  simp_rw [neg_neg, mul_sum, ← sum_add_distrib, ← mul_assoc, mul_comm _ (Φ _), mul_assoc,
    ← mul_add, map_neg, add_comm]
section signed
variable {Φ : ZMod N → ℂ}
lemma LFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_right_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaOdd_neg, mul_neg]
lemma LFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_left_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaEven_neg, neg_mul]
@[simp] lemma LFunction_apply_zero_of_even (hΦ : Φ.Even) :
    LFunction Φ 0 = -Φ 0 / 2 := by
  simp only [LFunction_def_even hΦ, neg_zero, cpow_zero, hurwitzZetaEven_apply_zero,
    toAddCircle_eq_zero, mul_ite, mul_div, mul_neg_one, mul_zero, sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, one_mul]
@[simp] lemma LFunction_neg_two_mul_nat_add_one (hΦ : Φ.Even) (n : ℕ) :
    LFunction Φ (-(2 * (n + 1))) = 0 := by
  simp only [LFunction_def_even hΦ, hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero,
    sum_const_zero, ← neg_mul]
@[simp] lemma LFunction_neg_two_mul_nat_sub_one (hΦ : Φ.Odd) (n : ℕ) :
    LFunction Φ (-(2 * n) - 1) = 0 := by
  simp only [LFunction_def_odd hΦ, hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero, ← neg_mul,
    sum_const_zero]
noncomputable def completedLFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  + N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s
@[simp] lemma completedLFunction_zero (s : ℂ) : completedLFunction (0 : ZMod N → ℂ) s = 0 := by
  simp only [completedLFunction, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, zero_add]
lemma completedLFunction_const_mul (a : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    completedLFunction (fun j ↦ a * Φ j) s = a * completedLFunction Φ s := by
  simp only [completedLFunction, mul_add, mul_sum]
  congr with i <;> ring
lemma completedLFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s := by
  suffices ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s = 0 by
    rw [completedLFunction, this, mul_zero, add_zero]
  refine (hΦ.mul_odd fun j ↦ ?_).sum_eq_zero
  rw [map_neg, completedHurwitzZetaOdd_neg]
lemma completedLFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s := by
  suffices ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s = 0 by
    rw [completedLFunction, this, mul_zero, zero_add]
  refine (hΦ.mul_even fun j ↦ ?_).sum_eq_zero
  rw [map_neg, completedHurwitzZetaEven_neg]
lemma completedLFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) :
    completedLFunction Φ s = Φ 1 * completedRiemannZeta s := by
  rw [completedLFunction_def_even (show Φ.Even from fun _ ↦ congr_arg Φ (Subsingleton.elim ..)),
    Nat.cast_one, one_cpow, one_mul, ← singleton_eq_univ 0, sum_singleton, map_zero,
    completedHurwitzZetaEven_zero, Subsingleton.elim 0 1]
noncomputable def completedLFunction₀ (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  + N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s
lemma differentiable_completedLFunction₀ (Φ : ZMod N → ℂ) :
    Differentiable ℂ (completedLFunction₀ Φ) := by
  refine .add ?_ ?_ <;>
  refine .mul (by fun_prop) (.sum fun i _ ↦ .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]
lemma completedLFunction_eq (Φ : ZMod N → ℂ) (s : ℂ) :
    completedLFunction Φ s =
      completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j) / (1 - s) := by
  simp only [completedLFunction, completedHurwitzZetaEven_eq, toAddCircle_eq_zero, div_eq_mul_inv,
    ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero, sum_sub_distrib, Fintype.sum_ite_eq',
    ← sum_mul, completedLFunction₀, mul_assoc]
  abel
lemma differentiableAt_completedLFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs₀ : s ≠ 0 ∨ Φ 0 = 0)
    (hs₁ : s ≠ 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt ℂ (completedLFunction Φ) s := by
  simp only [funext (completedLFunction_eq Φ), mul_div_assoc]
  refine ((differentiable_completedLFunction₀ _ _).sub ?_).sub ?_
  · 
    refine .mul (by fun_prop) (hs₀.elim ?_ ?_)
    · exact fun h ↦ (differentiableAt_const _).div differentiableAt_id h
    · exact fun h ↦ by simp only [h, funext zero_div, differentiableAt_const]
  · 
    refine .mul (by fun_prop) (hs₁.elim ?_ ?_)
    · exact fun h ↦ .div (by fun_prop) (by fun_prop) (by rwa [sub_ne_zero, ne_comm])
    · exact fun h ↦ by simp only [h, zero_div, differentiableAt_const]
lemma differentiable_completedLFunction (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) :
    Differentiable ℂ (completedLFunction Φ) :=
  fun s ↦ differentiableAt_completedLFunction Φ s (.inr hΦ₂) (.inr hΦ₃)
lemma LFunction_eq_completed_div_gammaFactor_even (hΦ : Φ.Even) (s : ℂ) (hs : s ≠ 0 ∨ Φ 0 = 0) :
    LFunction Φ s = completedLFunction Φ s / Gammaℝ s := by
  simp only [completedLFunction_def_even hΦ, LFunction_def_even hΦ, mul_div_assoc, sum_div]
  congr 2 with i
  rcases ne_or_eq i 0 with hi | rfl
  · rw [hurwitzZetaEven_def_of_ne_or_ne (.inl (hi ∘ toAddCircle_eq_zero.mp))]
  · rcases hs with hs | hΦ'
    · rw [hurwitzZetaEven_def_of_ne_or_ne (.inr hs)]
    · simp only [hΦ', map_zero, zero_mul]
lemma LFunction_eq_completed_div_gammaFactor_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s = completedLFunction Φ s / Gammaℝ (s + 1) := by
  simp only [LFunction_def_odd hΦ, completedLFunction_def_odd hΦ, hurwitzZetaOdd, mul_div_assoc,
    sum_div]
private lemma completedLFunction_one_sub_of_one_lt_even (hΦ : Φ.Even) {s : ℂ} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s := by
  have hs₀ : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hs₁ : s ≠ 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  suffices ∑ x, Φ x * completedCosZeta (toAddCircle x) s = completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_even hΦ, neg_sub, completedHurwitzZetaEven_one_sub, this]
  suffices ∑ x, Φ x * cosZeta (toAddCircle x) s = LFunction (𝓕 Φ) s by
    simpa only [cosZeta, Function.update_noteq hs₀, ← mul_div_assoc, ← sum_div,
      LFunction_eq_completed_div_gammaFactor_even (dft_even_iff.mpr hΦ) _ (.inl hs₀),
      div_left_inj' (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]
  simp only [cosZeta_eq, ← mul_div_assoc _ _ (2 : ℂ), mul_add, ← sum_div, sum_add_distrib,
    LFunction_dft Φ (.inr hs₁), map_neg, div_eq_iff (two_ne_zero' ℂ), mul_two, add_left_inj]
  exact Fintype.sum_equiv (.neg _) _ _ (by simp [hΦ _])
private lemma completedLFunction_one_sub_of_one_lt_odd (hΦ : Φ.Odd) {s : ℂ} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s := by
  suffices ∑ x, Φ x * completedSinZeta (toAddCircle x) s = I * completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_odd hΦ, neg_sub, completedHurwitzZetaOdd_one_sub, this,
      mul_assoc]
  suffices ∑ x, Φ x * sinZeta (toAddCircle x) s = I * LFunction (𝓕 Φ) s by
    have hs' : 0 < re (s + 1) := by simp only [add_re, one_re]; linarith
    simpa only [sinZeta, ← mul_div_assoc, ← sum_div, div_left_inj' (Gammaℝ_ne_zero_of_re_pos hs'),
      LFunction_eq_completed_div_gammaFactor_odd (dft_odd_iff.mpr hΦ)]
  calc ∑ x, Φ x * sinZeta (toAddCircle x) s
  _ = (∑ x, Φ x * expZeta (toAddCircle x) s) / (2 * I)
      - (∑ x, Φ x * expZeta (toAddCircle (-x)) s) / (2 * I) := by
    simp only [sinZeta_eq, ← mul_div_assoc, mul_sub, sub_div, sum_sub_distrib, sum_div, map_neg]
  _ = (∑ x, Φ (-x) * expZeta (toAddCircle (-x)) s) / (_) - (_) := by
    congrm ?_ / _ - _
    exact (Fintype.sum_equiv (.neg _) _ _ fun x ↦ by rfl).symm
  _ = -I⁻¹ * LFunction (𝓕 Φ) s := by
    simp only [hΦ _, neg_mul, sum_neg_distrib, LFunction_dft Φ (.inl hΦ.map_zero)]
    ring
  _ = I * LFunction (𝓕 Φ) s := by rw [inv_I, neg_neg]
theorem completedLFunction_one_sub_even (hΦ : Φ.Even) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ ∑ j, Φ j = 0) (hs₁ : s ≠ 1 ∨ Φ 0 = 0) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s := by
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * completedLFunction (𝓕 Φ) t
  let U := {t : ℂ | (t ≠ 0 ∨ ∑ j, Φ j = 0) ∧ (t ≠ 1 ∨ Φ 0 = 0)}
  have hsU : s ∈ U := ⟨hs₀, hs₁⟩
  have h2U : 2 ∈ U := ⟨.inl two_ne_zero, .inl (OfNat.ofNat_ne_one _)⟩
  have hUo : IsOpen U := (isOpen_compl_singleton.union isOpen_const).inter
    (isOpen_compl_singleton.union isOpen_const)
  have hUp : IsPreconnected U := by
    let Uc : Set ℂ := (if ∑ j, Φ j = 0 then ∅ else {0}) ∪ (if Φ 0 = 0 then ∅ else {1})
    have : Uc.Countable := by
      apply Countable.union <;>
      split_ifs <;>
      simp only [countable_singleton, countable_empty]
    convert (this.isConnected_compl_of_one_lt_rank ?_).isPreconnected using 1
    · ext x
      by_cases h : Φ 0 = 0 <;>
      by_cases h' : ∑ j, Φ j = 0 <;>
      simp [U, Uc, h, h', and_comm]
    · simp only [rank_real_complex, Nat.one_lt_ofNat]
  have hF : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    refine (differentiableAt_completedLFunction Φ _ ?_ ?_).comp t (differentiableAt_id.const_sub 1)
    exacts [ht.2.imp_left (sub_ne_zero.mpr ∘ Ne.symm), ht.1.imp_left sub_eq_self.not.mpr]
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    apply ((differentiableAt_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul
    apply differentiableAt_completedLFunction _ _ (ht.1.imp_right fun h ↦ dft_apply_zero Φ ▸ h)
    exact ht.2.imp_right (fun h ↦ by simp only [← dft_apply_zero, dft_dft, neg_zero, h, smul_zero])
  have hV : {z | 1 < re z} ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := eventually_of_mem hV <| fun t ht ↦ by
    simpa only [F, G, pow_zero, mul_one] using completedLFunction_one_sub_of_one_lt_even hΦ ht
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUp h2U hFG hsU
theorem completedLFunction_one_sub_odd (hΦ : Φ.Odd) (s : ℂ) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s := by
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * I * completedLFunction (𝓕 Φ) t
  have hF : Differentiable ℂ F := (differentiable_completedLFunction hΦ.map_zero
    hΦ.sum_eq_zero).comp (differentiable_id.const_sub 1)
  have hG : Differentiable ℂ G := by
    apply (((differentiable_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul_const _).mul
    rw [← dft_odd_iff] at hΦ
    exact differentiable_completedLFunction hΦ.map_zero hΦ.sum_eq_zero
  have : {z | 1 < re z} ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := by filter_upwards [this] with t ht
    using completedLFunction_one_sub_of_one_lt_odd hΦ ht
  rw [← analyticOnNhd_univ_iff_differentiable] at hF hG
  exact congr_fun (hF.eq_of_eventuallyEq hG hFG) s
end signed
end ZMod