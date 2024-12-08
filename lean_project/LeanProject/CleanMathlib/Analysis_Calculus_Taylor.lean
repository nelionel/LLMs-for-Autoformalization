import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
open scoped Interval Topology Nat
open Set
variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def taylorCoeffWithin (f : ℝ → E) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) : E :=
  (k ! : ℝ)⁻¹ • iteratedDerivWithin k f s x₀
noncomputable def taylorWithin (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) : PolynomialModule ℝ E :=
  (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ k (taylorCoeffWithin f k s x₀))
noncomputable def taylorWithinEval (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)
theorem taylorWithin_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ +
      PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ (n + 1) (taylorCoeffWithin f (n + 1) s x₀)) := by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]
@[simp]
theorem taylorWithinEval_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f (n + 1) s x₀ x = taylorWithinEval f n s x₀ x +
      (((n + 1 : ℝ) * n !)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀ := by
  simp_rw [taylorWithinEval, taylorWithin_succ, LinearMap.map_add, PolynomialModule.comp_eval]
  congr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    PolynomialModule.eval_single, mul_inv_rev]
  dsimp only [taylorCoeffWithin]
  rw [← mul_smul, mul_comm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_inv_rev]
@[simp]
theorem taylor_within_zero_eval (f : ℝ → E) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f 0 s x₀ x = f x₀ := by
  dsimp only [taylorWithinEval]
  dsimp only [taylorWithin]
  dsimp only [taylorCoeffWithin]
  simp
@[simp]
theorem taylorWithinEval_self (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithinEval f n s x₀ x₀ = f x₀ := by
  induction n with
  | zero => exact taylor_within_zero_eval _ _ _ _
  | succ k hk => simp [hk]
theorem taylor_within_apply (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f n s x₀ x =
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀ := by
  induction n with
  | zero => simp
  | succ k hk =>
    rw [taylorWithinEval_succ, Finset.sum_range_succ, hk]
    simp [Nat.factorial]
theorem continuousOn_taylorWithinEval {f : ℝ → E} {x : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ n f s) :
    ContinuousOn (fun t => taylorWithinEval f n s t x) s := by
  simp_rw [taylor_within_apply]
  refine continuousOn_finset_sum (Finset.range (n + 1)) fun i hi => ?_
  refine (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow _)).smul ?_
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs] at hf
  cases' hf with hf_left
  specialize hf_left i
  simp only [Finset.mem_range] at hi
  refine hf_left ?_
  simp only [WithTop.coe_le_coe, Nat.cast_le, Nat.lt_succ_iff.mp hi]
theorem monomial_has_deriv_aux (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => (x - y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t := by
  simp_rw [sub_eq_neg_add]
  rw [← neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ← mul_assoc]
  convert HasDerivAt.pow (n + 1) ((hasDerivAt_id t).neg.add_const x)
  simp only [Nat.cast_add, Nat.cast_one]
theorem hasDerivWithinAt_taylor_coeff_within {f : ℝ → E} {x y : ℝ} {k : ℕ} {s t : Set ℝ}
    (ht : UniqueDiffWithinAt ℝ t y) (hs : s ∈ 𝓝[t] y)
    (hf : DifferentiableWithinAt ℝ (iteratedDerivWithin (k + 1) f s) s y) :
    HasDerivWithinAt
      (fun z => (((k + 1 : ℝ) * k !)⁻¹ * (x - z) ^ (k + 1)) • iteratedDerivWithin (k + 1) f s z)
      ((((k + 1 : ℝ) * k !)⁻¹ * (x - y) ^ (k + 1)) • iteratedDerivWithin (k + 2) f s y -
        ((k ! : ℝ)⁻¹ * (x - y) ^ k) • iteratedDerivWithin (k + 1) f s y) t y := by
  replace hf :
    HasDerivWithinAt (iteratedDerivWithin (k + 1) f s) (iteratedDerivWithin (k + 2) f s y) t y := by
    convert (hf.mono_of_mem_nhdsWithin hs).hasDerivWithinAt using 1
    rw [iteratedDerivWithin_succ (ht.mono_nhds (nhdsWithin_le_iff.mpr hs))]
    exact (derivWithin_of_mem_nhdsWithin hs ht hf).symm
  have : HasDerivWithinAt (fun t => ((k + 1 : ℝ) * k !)⁻¹ * (x - t) ^ (k + 1))
      (-((k ! : ℝ)⁻¹ * (x - y) ^ k)) t y := by
    have : -((k ! : ℝ)⁻¹ * (x - y) ^ k) = ((k + 1 : ℝ) * k !)⁻¹ * (-(k + 1) * (x - y) ^ k) := by
      field_simp; ring
    rw [this]
    exact (monomial_has_deriv_aux y x _).hasDerivWithinAt.const_mul _
  convert this.smul hf using 1
  field_simp
  rw [neg_div, neg_smul, sub_eq_add_neg]
theorem hasDerivWithinAt_taylorWithinEval {f : ℝ → E} {x y : ℝ} {n : ℕ} {s s' : Set ℝ}
    (hs'_unique : UniqueDiffWithinAt ℝ s' y) (hs_unique : UniqueDiffOn ℝ s) (hs' : s' ∈ 𝓝[s] y)
    (hy : y ∈ s') (h : s' ⊆ s) (hf : ContDiffOn ℝ n f s)
    (hf' : DifferentiableWithinAt ℝ (iteratedDerivWithin n f s) s y) :
    HasDerivWithinAt (fun t => taylorWithinEval f n s t x)
      (((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f s y) s' y := by
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul]
    simp only [iteratedDerivWithin_zero] at hf'
    rw [iteratedDerivWithin_one (hs_unique _ (h hy))]
    exact hf'.hasDerivWithinAt.mono h
  | succ k hk =>
    simp_rw [Nat.add_succ, taylorWithinEval_succ]
    simp only [add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have coe_lt_succ : (k : WithTop ℕ) < k.succ := Nat.cast_lt.2 k.lt_succ_self
    have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k f s) s' :=
      (hf.differentiableOn_iteratedDerivWithin (mod_cast coe_lt_succ) hs_unique).mono h
    specialize hk hf.of_succ ((hdiff y hy).mono_of_mem_nhdsWithin hs')
    convert hk.add (hasDerivWithinAt_taylor_coeff_within hs'_unique
      (nhdsWithin_mono _ h self_mem_nhdsWithin) hf') using 1
    exact (add_sub_cancel _ _).symm
theorem taylorWithinEval_hasDerivAt_Ioo {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ} (hx : a < b)
    (ht : t ∈ Ioo a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    HasDerivAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) t :=
  have h_nhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have h_nhds' : Ioo a b ∈ 𝓝[Icc a b] t := nhdsWithin_le_nhds h_nhds
  (hasDerivWithinAt_taylorWithinEval (uniqueDiffWithinAt_Ioo ht) (uniqueDiffOn_Icc hx) h_nhds' ht
    Ioo_subset_Icc_self hf <| (hf' t ht).mono_of_mem_nhdsWithin h_nhds').hasDerivAt h_nhds
theorem hasDerivWithinAt_taylorWithinEval_at_Icc {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ}
    (hx : a < b) (ht : t ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t :=
  hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx t ht) (uniqueDiffOn_Icc hx)
    self_mem_nhdsWithin ht rfl.subset hf (hf' t ht)
theorem taylor_mean_remainder {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x))
    (gcont : ContinuousOn g (Icc x₀ x))
    (gdiff : ∀ x_1 : ℝ, x_1 ∈ Ioo x₀ x → HasDerivAt g (g' x_1) x_1)
    (g'_ne : ∀ x_1 : ℝ, x_1 ∈ Ioo x₀ x → g' x_1 ≠ 0) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
    ((x - x') ^ n / n ! * (g x - g x₀) / g' x') • iteratedDerivWithin (n + 1) f (Icc x₀ x) x' := by
  rcases exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (Icc x₀ x) t x)
      (fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc x₀ x) t) hx
      (continuousOn_taylorWithinEval (uniqueDiffOn_Icc hx) hf)
      (fun _ hy => taylorWithinEval_hasDerivAt_Ioo x hx hy hf hf') g g' gcont gdiff with ⟨y, hy, h⟩
  use y, hy
  simp only [taylorWithinEval_self] at h
  rw [mul_comm, ← div_left_inj' (g'_ne y hy), mul_div_cancel_right₀ _ (g'_ne y hy)] at h
  rw [← h]
  field_simp [g'_ne y hy]
  ring
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have gcont : ContinuousOn (fun t : ℝ => (x - t) ^ (n + 1)) (Icc x₀ x) := by fun_prop
  have xy_ne : ∀ y : ℝ, y ∈ Ioo x₀ x → (x - y) ^ n ≠ 0 := by
    intro y hy
    refine pow_ne_zero _ ?_
    rw [mem_Ioo] at hy
    rw [sub_ne_zero]
    exact hy.2.ne'
  have hg' : ∀ y : ℝ, y ∈ Ioo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 := fun y hy =>
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n)) (xy_ne y hy)
  rcases taylor_mean_remainder hx hf hf' gcont (fun y _ => monomial_has_deriv_aux y x _) hg' with
    ⟨y, hy, h⟩
  use y, hy
  simp only [sub_self, zero_pow, Ne, Nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h
  rw [h, neg_div, ← div_neg, neg_mul, neg_neg]
  field_simp [xy_ne y hy, Nat.factorial]; ring
theorem taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) := by
  have gcont : ContinuousOn id (Icc x₀ x) := by fun_prop
  have gdiff : ∀ x_1 : ℝ, x_1 ∈ Ioo x₀ x → HasDerivAt id ((fun _ : ℝ => (1 : ℝ)) x_1) x_1 :=
    fun _ _ => hasDerivAt_id _
  rcases taylor_mean_remainder hx hf hf' gcont gdiff fun _ _ => by simp with ⟨y, hy, h⟩
  use y, hy
  rw [h]
  field_simp [n.factorial_ne_zero]
  ring
theorem taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n ! := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Icc_self, mem_singleton_iff] at hx
    simp [hx]
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_succ_self)
      (uniqueDiffOn_Icc h)
  have h' : ∀ y ∈ Ico a x,
      ‖((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤
        (n ! : ℝ)⁻¹ * |x - a| ^ n * C := by
    rintro y ⟨hay, hyx⟩
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    · rw [abs_mul, abs_pow, abs_inv, Nat.abs_cast]
      gcongr
      exact sub_nonneg.2 hyx.le
    · exact hC y ⟨hay, hyx.le.trans hx.2⟩
  have A : ∀ t ∈ Icc a x, HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((↑n !)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a x) t := by
    intro t ht
    have I : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2
    exact (hasDerivWithinAt_taylorWithinEval_at_Icc x h (I ht) hf.of_succ hf').mono I
  have := norm_image_sub_le_of_norm_deriv_le_segment' A h' x (right_mem_Icc.2 hx.1)
  simp only [taylorWithinEval_self] at this
  refine this.trans_eq ?_
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  ring
theorem exists_taylor_mean_remainder_bound {f : ℝ → E} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine ⟨0, fun x hx => ?_⟩
    have : x = a := by simpa [← le_antisymm_iff] using hx
    simp [← this]
  let g : ℝ → ℝ := fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖
  use SupSet.sSup (g '' Icc a b) / (n !)
  intro x hx
  rw [div_mul_eq_mul_div₀]
  refine taylor_mean_remainder_bound hab hf hx fun y => ?_
  exact (hf.continuousOn_iteratedDerivWithin rfl.le <| uniqueDiffOn_Icc h).norm.le_sSup_image_Icc