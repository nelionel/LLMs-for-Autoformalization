import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Data.Real.EReal
open Complex
noncomputable def LSeries.abscissaOfAbsConv (f : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | LSeriesSummable f x}
lemma LSeries.abscissaOfAbsConv_congr {f g : ℕ → ℂ} (h : ∀ {n}, n ≠ 0 → f n = g n) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
  congr_arg sInf <| congr_arg _ <| Set.ext fun x ↦ LSeriesSummable_congr x h
open Filter in
lemma LSeries.abscissaOfAbsConv_congr' {f g : ℕ → ℂ} (h : f =ᶠ[atTop] g) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
  congr_arg sInf <| congr_arg _ <| Set.ext fun x ↦ LSeriesSummable_congr' x h
open LSeries
lemma LSeriesSummable_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) : LSeriesSummable f s := by
  simp only [abscissaOfAbsConv, sInf_lt_iff, Set.mem_image, Set.mem_setOf_eq,
    exists_exists_and_eq_and, EReal.coe_lt_coe_iff] at hs
  obtain ⟨y, hy, hys⟩ := hs
  exact hy.of_re_le_re <| ofReal_re y ▸ hys.le
lemma LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re {f : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfAbsConv f < s.re) :
    ∃ x : ℝ, x < s.re ∧ LSeriesSummable f x := by
  obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hs
  exact ⟨x, EReal.coe_lt_coe_iff.mp hx₂, LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁⟩
lemma LSeriesSummable.abscissaOfAbsConv_le {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    abscissaOfAbsConv f ≤ s.re := by
  refine sInf_le <| Membership.mem.out ?_
  simp only [Set.mem_setOf_eq, Set.mem_image, EReal.coe_eq_coe_iff, exists_eq_right]
  exact h.of_re_le_re <| by simp only [ofReal_re, le_refl]
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : ℕ → ℂ} {x : ℝ}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  refine sInf_le_iff.mpr fun y hy ↦ ?_
  simp only [mem_lowerBounds, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hy
  have H (a : EReal) : x < a → y ≤ a := by
    induction' a with a₀
    · simp only [not_lt_bot, le_bot_iff, IsEmpty.forall_iff]
    · exact_mod_cast fun ha ↦ hy a₀ (h a₀ ha)
    · simp only [EReal.coe_lt_top, le_top, forall_true_left]
  exact Set.Ioi_subset_Ici_iff.mp H
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : ℕ → ℂ} {x : EReal}
    (h : ∀ y : ℝ, x < y → LSeriesSummable f y) :
    abscissaOfAbsConv f ≤ x := by
  induction' x with y
  · refine le_of_eq <| sInf_eq_bot.mpr fun y hy ↦ ?_
    induction' y with z
    · simp only [gt_iff_lt, lt_self_iff_false] at hy
    · exact ⟨z - 1,  ⟨z-1, h (z - 1) <| EReal.bot_lt_coe _, rfl⟩, by norm_cast; exact sub_one_lt z⟩
    · exact ⟨0, ⟨0, h 0 <| EReal.bot_lt_coe 0, rfl⟩, EReal.zero_lt_top⟩
  · exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable <| by exact_mod_cast h
  · exact le_top
lemma LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow {f : ℕ → ℂ} {x : ℝ}
    (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C * n ^ x) : abscissaOfAbsConv f ≤ x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_le_const_mul_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
    |>.abscissaOfAbsConv_le.trans_lt hy₂).false
open Filter in
lemma LSeries.abscissaOfAbsConv_le_of_isBigO_rpow {f : ℕ → ℂ} {x : ℝ}
    (h : f =O[atTop] fun n ↦ (n : ℝ) ^ x) :
    abscissaOfAbsConv f ≤ x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_isBigO_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
    |>.abscissaOfAbsConv_le.trans_lt hy₂).false
lemma LSeries.abscissaOfAbsConv_le_of_le_const {f : ℕ → ℂ} (h : ∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C) :
    abscissaOfAbsConv f ≤ 1 := by
  convert abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) ?_
  · simp only [EReal.coe_zero, zero_add]
  · simpa only [norm_eq_abs, Real.rpow_zero, mul_one] using h
open Filter in
lemma LSeries.abscissaOfAbsConv_le_one_of_isBigO_one {f : ℕ → ℂ} (h : f =O[atTop] (1 : ℕ → ℝ)) :
    abscissaOfAbsConv f ≤ 1 := by
  convert abscissaOfAbsConv_le_of_isBigO_rpow (x := 0) ?_
  · simp only [EReal.coe_zero, zero_add]
  · simpa only [Real.rpow_zero] using h
lemma LSeries.summable_real_of_abscissaOfAbsConv_lt {f : ℕ → ℝ} {x : ℝ}
    (h : abscissaOfAbsConv (f ·) < x) :
    Summable fun n : ℕ ↦ f n / (n : ℝ) ^ x := by
  have h' : abscissaOfAbsConv (f ·) < (x : ℂ).re := by simpa only [ofReal_re] using h
  have := LSeriesSummable_of_abscissaOfAbsConv_lt_re h'
  rw [LSeriesSummable, show term _ _ = fun n ↦ _ from rfl] at this
  conv at this =>
    enter [1, n]
    rw [term_def, show (n : ℂ) = (n : ℝ) from rfl, ← ofReal_cpow n.cast_nonneg, ← ofReal_div,
      show (0 : ℂ) = (0 : ℝ) from rfl, ← apply_ite]
  rw [summable_ofReal] at this
  refine this.congr_cofinite ?_
  filter_upwards [Set.Finite.compl_mem_cofinite <| Set.finite_singleton 0] with n hn
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hn
  exact if_neg hn