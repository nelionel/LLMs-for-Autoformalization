import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
open HurwitzZeta Complex Finset Classical ZMod Filter
open scoped Real Topology
namespace DirichletCharacter
variable {N : ℕ} [NeZero N]
@[pp_nodot]
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s
@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs
lemma deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    deriv (LFunction χ) s = deriv (LSeries (χ ·)) s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz
@[fun_prop]
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)
@[fun_prop]
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)
@[simp]
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
    LFunction χ (-(2 * (n + 1))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n
@[simp]
lemma Even.LFunction_neg_two_mul_nat {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) [NeZero n] :
    LFunction χ (-(2 * n)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact_mod_cast hχ.LFunction_neg_two_mul_nat_add_one m
@[simp] lemma Odd.LFunction_neg_two_mul_nat_sub_one
  {χ : DirichletCharacter ℂ N} (hχ : Odd χ) (n : ℕ) :
    LFunction χ (-(2 * n) - 1) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n
private lemma LFunction_changeLevel_aux {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _)
      |>.isPreconnected
  have hne : 2 ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (g := fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction _ _ (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .finset_prod fun i h ↦ ?_
    have : NeZero i := ⟨(Nat.pos_of_mem_primeFactors h).ne'⟩
    fun_prop
  · refine eventually_of_mem ?_  (fun t (ht : 1 < t.re) ↦ ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num : 1 < (2 : ℂ).re)
    · simpa only [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht
lemma LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rcases h with h | h
  · have hχ : changeLevel hMN χ ≠ 1 := h ∘ (changeLevel_eq_one_iff hMN).mp
    have h' : Continuous fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * ↑p ^ (-s)) :=
      (differentiable_LFunction h).continuous.mul <| continuous_finset_prod _ fun p hp ↦ by
        have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        fun_prop
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h ↦ LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h
noncomputable abbrev LFunctionTrivChar (N : ℕ) [NeZero N] :=
  (1 : DirichletCharacter ℂ N).LFunction
lemma LFunctionTrivChar_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar N s = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1), LFunctionTrivChar, ← changeLevel_one N.one_dvd, mul_comm]
  convert LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]
lemma LFunctionTrivChar_residue_one :
    Tendsto (fun s ↦ (s - 1) * LFunctionTrivChar N s) (𝓝[≠] 1)
      (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  have H : (fun s ↦ (s - 1) * LFunctionTrivChar N s) =ᶠ[𝓝[≠] 1]
        fun s ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ ?_
    rw [mul_left_comm, LFunctionTrivChar_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s ↦ ∏ p ∈ N.primeFactors, _) ?_ riemannZeta_residue_one
  refine tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto ?_ 1
  exact continuous_finset_prod _ fun p hp ↦ by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
section gammaFactor
omit [NeZero N] 
noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) :=
  if χ.Even then Gammaℝ s else Gammaℝ (s + 1)
lemma Even.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ) :
    gammaFactor χ s = Gammaℝ s := by
  simp only [gammaFactor, hχ, ↓reduceIte]
lemma Odd.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + 1) := by
  simp only [gammaFactor, hχ.not_even, ↓reduceIte]
end gammaFactor
@[pp_nodot] noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ZMod.completedLFunction χ s
lemma completedLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    completedLFunction χ = completedRiemannZeta := by
  ext; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]
lemma differentiableAt_completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ N ≠ 1) (hs₁ : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (completedLFunction χ) s :=
  ZMod.differentiableAt_completedLFunction _ _ (by have := χ.map_zero'; tauto)
    (by have := χ.sum_eq_zero_of_ne_one; tauto)
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) := by
  refine fun s ↦ differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h : s ≠ 0 ∨ N ≠ 1) : LFunction χ s = completedLFunction χ s / gammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ <;>
  rw [hχ.gammaFactor_def]
  · exact LFunction_eq_completed_div_gammaFactor_even hχ.to_fun _ (h.imp_right χ.map_zero')
  · apply LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun
noncomputable def rootNumber (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : ℂ)
lemma rootNumber_modOne (χ : DirichletCharacter ℂ 1) : rootNumber χ = 1 := by
  simp only [rootNumber, gaussSum, ← singleton_eq_univ (1 : ZMod 1), sum_singleton, map_one,
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _), one_mul,
    (show χ.Even from map_one _), ite_true, pow_zero, div_one, Nat.cast_one, one_cpow]
namespace IsPrimitive
theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
  rcases eq_or_ne N 1 with rfl | hN
  · simp only [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, Nat.cast_one, one_cpow,
      rootNumber_modOne, one_mul]
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h ↦ hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one (NeZero.ne _)] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  rw [rootNumber, ← mul_comm_div, ← mul_comm_div, ← cpow_sub _ _ (NeZero.ne _), sub_sub, add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) /  ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction, completedLFunction_one_sub_odd h.to_fun,
        pow_one, h, div_I, mul_neg_one, ← neg_mul, neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j ↦ χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul j, map_mul, mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)):= by
    rw [completedLFunction, completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (isUnit_one.neg), mul_one]
end IsPrimitive
end DirichletCharacter
namespace DirichletCharacter
open Complex
section trivial
variable (n : ℕ) [NeZero n]
noncomputable abbrev LFunctionTrivChar₁ : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * LFunctionTrivChar n s) 1
    (∏ p ∈ n.primeFactors, (1 - (p : ℂ)⁻¹))
lemma LFunctionTrivChar₁_apply_one_ne_zero : LFunctionTrivChar₁ n 1 ≠ 0 := by
  simp only [Function.update_same]
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  simpa only [ne_eq, sub_ne_zero, one_eq_inv, Nat.cast_eq_one]
    using (Nat.prime_of_mem_primeFactors hp).ne_one
lemma differentiable_LFunctionTrivChar₁ : Differentiable ℂ (LFunctionTrivChar₁ n) := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s ↦ (s - 1) * LFunctionTrivChar n s)
    (fun _ hs ↦ DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all [hs]))
   fun _ hs ↦ Function.update_noteq (Set.mem_diff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa only [continuousWithinAt_compl_self, continuousAt_update_same]
    using LFunctionTrivChar_residue_one
lemma deriv_LFunctionTrivChar₁_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv (LFunctionTrivChar₁ n) s =
      (s - 1) * deriv (LFunctionTrivChar n) s + LFunctionTrivChar n s := by
  have H : deriv (LFunctionTrivChar₁ n) s =
      deriv (fun w ↦ (w - 1) * LFunctionTrivChar n w) s := by
    refine eventuallyEq_iff_exists_mem.mpr ?_ |>.deriv_eq
    exact ⟨_, isOpen_ne.mem_nhds hs, fun _ hw ↦ Function.update_noteq (Set.mem_setOf.mp hw) ..⟩
  rw [H, deriv_mul (by fun_prop) (differentiableAt_LFunction _ s (.inl hs)), deriv_sub_const,
    deriv_id'', one_mul, add_comm]
lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁ :
    ContinuousOn (fun s ↦ -deriv (LFunctionTrivChar₁ n) s / LFunctionTrivChar₁ n s)
      {s | s = 1 ∨ LFunctionTrivChar n s ≠ 0} := by
  simp_rw [neg_div]
  have h := differentiable_LFunctionTrivChar₁ n
  refine ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun w hw ↦ ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · exact LFunctionTrivChar₁_apply_one_ne_zero _
  · rw [LFunctionTrivChar₁, Function.update_noteq hw', mul_ne_zero_iff]
    exact ⟨sub_ne_zero_of_ne hw', (Set.mem_setOf.mp hw).resolve_left hw'⟩
end trivial
section nontrivial
variable {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
lemma continuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ ≠ 1) :
    ContinuousOn (fun s ↦ -deriv (LFunction χ) s / LFunction χ s) {s | LFunction χ s ≠ 0} := by
  simp only [neg_div]
  have h := differentiable_LFunction hχ
  exact ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun _ hw ↦ hw).neg
end nontrivial
end DirichletCharacter