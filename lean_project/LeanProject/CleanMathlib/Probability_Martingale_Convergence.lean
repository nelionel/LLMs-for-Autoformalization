import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Upcrossing
open TopologicalSpace Filter MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology
namespace MeasureTheory
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} {R : ℝ≥0}
section AeConvergence
theorem not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f ω ≠ ∞) :
    ¬((∃ᶠ n in atTop, f n ω < a) ∧ ∃ᶠ n in atTop, b < f n ω) := by
  rw [← lt_top_iff_ne_top, upcrossings_lt_top_iff] at hω
  replace hω : ∃ k, ∀ N, upcrossingsBefore a b f N ω < k := by
    obtain ⟨k, hk⟩ := hω
    exact ⟨k + 1, fun N => lt_of_le_of_lt (hk N) k.lt_succ_self⟩
  rintro ⟨h₁, h₂⟩
  rw [frequently_atTop] at h₁ h₂
  refine Classical.not_not.2 hω ?_
  push_neg
  intro k
  induction' k with k ih
  · simp only [zero_le, exists_const]
  · obtain ⟨N, hN⟩ := ih
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁
    exact ⟨N₂ + 1, Nat.succ_le_of_lt <|
      lt_of_le_of_lt hN (upcrossingsBefore_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩
theorem upcrossings_eq_top_of_frequently_lt (hab : a < b) (h₁ : ∃ᶠ n in atTop, f n ω < a)
    (h₂ : ∃ᶠ n in atTop, b < f n ω) : upcrossings a b f ω = ∞ :=
  by_contradiction fun h => not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩
theorem tendsto_of_uncrossing_lt_top (hf₁ : liminf (fun n => (‖f n ω‖₊ : ℝ≥0∞)) atTop < ∞)
    (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) :
    ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  by_cases h : IsBoundedUnder (· ≤ ·) atTop fun n => |f n ω|
  · rw [isBoundedUnder_le_abs] at h
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ h.1 h.2
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (Rat.cast_lt.1 hab)).ne
  · obtain ⟨a, b, hab, h₁, h₂⟩ := ENNReal.exists_upcrossings_of_not_bounded_under hf₁.ne h
    exact
      False.elim ((hf₂ a b hab).ne (upcrossings_eq_top_of_frequently_lt (Rat.cast_lt.2 hab) h₁ h₂))
theorem Submartingale.upcrossings_ae_lt_top' [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) (hab : a < b) : ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ := by
  refine ae_lt_top (hf.adapted.measurable_upcrossings hab) ?_
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le] at this
  · refine (lt_of_le_of_lt this (ENNReal.div_lt_top ?_ ?_)).ne
    · have hR' : ∀ n, ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ R + ‖a‖₊ * μ Set.univ := by
        simp_rw [eLpNorm_one_eq_lintegral_nnnorm] at hbdd
        intro n
        refine (lintegral_mono ?_ : ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ ∫⁻ ω, ‖f n ω‖₊ + ‖a‖₊ ∂μ).trans ?_
        · intro ω
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ENNReal.coe_add, ENNReal.coe_le_coe]
          exact nnnorm_add_le _ _
        · simp_rw [lintegral_add_right _ measurable_const, lintegral_const]
          exact add_le_add (hbdd _) le_rfl
      refine ne_of_lt (iSup_lt_iff.2 ⟨R + ‖a‖₊ * μ Set.univ, ENNReal.add_lt_top.2
        ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)⟩,
        fun n => le_trans ?_ (hR' n)⟩)
      refine lintegral_mono fun ω => ?_
      rw [ENNReal.ofReal_le_iff_le_toReal, ENNReal.coe_toReal, coe_nnnorm]
      · by_cases hnonneg : 0 ≤ f n ω - a
        · rw [posPart_eq_self.2 hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        · rw [posPart_eq_zero.2 (not_le.1 hnonneg).le]
          exact norm_nonneg _
      · simp only [Ne, ENNReal.coe_ne_top, not_false_iff]
    · simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
  · simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le, true_or]
  · simp only [Ne, ENNReal.ofReal_ne_top, not_false_iff, true_or]
theorem Submartingale.upcrossings_ae_lt_top [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  rintro a b hab
  exact hf.upcrossings_ae_lt_top' hbdd (Rat.cast_lt.2 hab)
theorem Submartingale.exists_ae_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.upcrossings_ae_lt_top hbdd, ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero
    (fun n => (hf.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with ω h₁ h₂
  exact tendsto_of_uncrossing_lt_top h₂ h₁
theorem Submartingale.exists_ae_trim_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ.trim (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _ : ⨆ n, ℱ n ≤ m0),
      ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  letI := (⨆ n, ℱ n)
  rw [ae_iff, trim_measurableSet_eq]
  · exact hf.exists_ae_tendsto_of_bdd hbdd
  · exact MeasurableSet.compl <| measurableSet_exists_tendsto
      fun n => (hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩) le_rfl
theorem Submartingale.ae_tendsto_limitProcess [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) := by
  classical
  suffices
      ∃ g, StronglyMeasurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) by
    rw [limitProcess, dif_pos this]
    exact (Classical.choose_spec this).2
  set g' : Ω → ℝ := fun ω => if h : ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) then h.choose else 0
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hg' : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g' ω)) := by
    filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dif_pos hω]
    exact hω.choose_spec
  have hg'm : @AEStronglyMeasurable _ _ _ (⨆ n, ℱ n) g' (μ.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (fun n => ((hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n)
        le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω
    exact hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩
theorem Submartingale.memℒp_limitProcess {p : ℝ≥0∞} (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) : Memℒp (ℱ.limitProcess f μ) p μ :=
  memℒp_limitProcess_of_eLpNorm_bdd
    (fun n => ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) hbdd
end AeConvergence
section L1Convergence
variable [IsFiniteMeasure μ] {g : Ω → ℝ}
theorem Submartingale.tendsto_eLpNorm_one_limitProcess (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) 1 μ) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hunif.2.2
  have hmeas : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hf.stronglyMeasurable n).mono (ℱ.le _)).aestronglyMeasurable
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memℒp_limitProcess_of_eLpNorm_bdd hmeas hR) hunif.2.1
    (tendstoInMeasure_of_tendsto_ae hmeas <| hf.ae_tendsto_limitProcess hR)
@[deprecated (since := "2024-07-27")]
alias Submartingale.tendsto_snorm_one_limitProcess := Submartingale.tendsto_eLpNorm_one_limitProcess
theorem Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) :=
  let ⟨_, hR⟩ := hunif.2.2
  hf.ae_tendsto_limitProcess hR
theorem Martingale.eq_condexp_of_tendsto_eLpNorm {μ : Measure Ω} (hf : Martingale f ℱ μ)
    (hg : Integrable g μ) (hgtends : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) (n : ℕ) :
    f n =ᵐ[μ] μ[g|ℱ n] := by
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff (((hf.stronglyMeasurable n).mono (ℱ.le _)).sub
    (stronglyMeasurable_condexp.mono (ℱ.le _))).aestronglyMeasurable one_ne_zero]
  have ht : Tendsto (fun m => eLpNorm (μ[f m - g|ℱ n]) 1 μ) atTop (𝓝 0) :=
    haveI hint : ∀ m, Integrable (f m - g) μ := fun m => (hf.integrable m).sub hg
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends (fun m => zero_le _)
      fun m => eLpNorm_one_condexp_le_eLpNorm _
  have hev : ∀ m ≥ n, eLpNorm (μ[f m - g|ℱ n]) 1 μ = eLpNorm (f n - μ[g|ℱ n]) 1 μ := by
    refine fun m hm => eLpNorm_congr_ae ((condexp_sub (hf.integrable m) hg).trans ?_)
    filter_upwards [hf.2 n m hm] with x hx
    simp only [hx, Pi.sub_apply]
  exact tendsto_nhds_unique (tendsto_atTop_of_eventually_const hev) ht
@[deprecated (since := "2024-07-27")]
alias Martingale.eq_condexp_of_tendsto_snorm := Martingale.eq_condexp_of_tendsto_eLpNorm
theorem Martingale.ae_eq_condexp_limitProcess (hf : Martingale f ℱ μ)
    (hbdd : UniformIntegrable f 1 μ) (n : ℕ) : f n =ᵐ[μ] μ[ℱ.limitProcess f μ|ℱ n] :=
  let ⟨_, hR⟩ := hbdd.2.2
  hf.eq_condexp_of_tendsto_eLpNorm ((memℒp_limitProcess_of_eLpNorm_bdd hbdd.1 hR).integrable le_rfl)
    (hf.submartingale.tendsto_eLpNorm_one_limitProcess hbdd) n
theorem Integrable.tendsto_ae_condexp (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g|ℱ n]) x) atTop (𝓝 (g x)) := by
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hunif : UniformIntegrable (fun n => μ[g|ℱ n]) 1 μ :=
    hg.uniformIntegrable_condexp_filtration
  obtain ⟨R, hR⟩ := hunif.2.2
  have hlimint : Integrable (ℱ.limitProcess (fun n => μ[g|ℱ n]) μ) μ :=
    (memℒp_limitProcess_of_eLpNorm_bdd hunif.1 hR).integrable le_rfl
  suffices g =ᵐ[μ] ℱ.limitProcess (fun n x => (μ[g|ℱ n]) x) μ by
    filter_upwards [this, (martingale_condexp g ℱ μ).submartingale.ae_tendsto_limitProcess hR] with
      x heq ht
    rwa [heq]
  have : ∀ n s, MeasurableSet[ℱ n] s →
      ∫ x in s, g x ∂μ = ∫ x in s, ℱ.limitProcess (fun n x => (μ[g|ℱ n]) x) μ x ∂μ := by
    intro n s hs
    rw [← setIntegral_condexp (ℱ.le n) hg hs, ← setIntegral_condexp (ℱ.le n) hlimint hs]
    refine setIntegral_congr_ae (ℱ.le _ _ hs) ?_
    filter_upwards [(martingale_condexp g ℱ μ).ae_eq_condexp_limitProcess hunif n] with x hx _
    rw [hx]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hle (fun s _ _ => hg.integrableOn)
    (fun s _ _ => hlimint.integrableOn) (fun s hs => ?_) hgmeas.aeStronglyMeasurable'
    stronglyMeasurable_limitProcess.aeStronglyMeasurable'
  apply @MeasurableSpace.induction_on_inter _ _ _ (⨆ n, ℱ n)
    (MeasurableSpace.measurableSpace_iSup_eq ℱ) _ _ _ _ _ _ hs
  · rintro s ⟨n, hs⟩ t ⟨m, ht⟩ -
    by_cases hnm : n ≤ m
    · exact ⟨m, (ℱ.mono hnm _ hs).inter ht⟩
    · exact ⟨n, hs.inter (ℱ.mono (not_le.1 hnm).le _ ht)⟩
  · simp only [measure_empty, ENNReal.zero_lt_top, Measure.restrict_empty, integral_zero_measure,
      forall_true_left]
  · rintro t ⟨n, ht⟩ -
    exact this n _ ht
  · rintro t htmeas ht -
    have hgeq := @setIntegral_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas (hg.trim hle hgmeas)
    have hheq := @setIntegral_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas
      (hlimint.trim hle stronglyMeasurable_limitProcess)
    rw [setIntegral_trim hle hgmeas htmeas.compl,
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas.compl, hgeq, hheq, ←
      setIntegral_trim hle hgmeas htmeas, ←
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas, ← integral_trim hle hgmeas, ←
      integral_trim hle stronglyMeasurable_limitProcess, ← setIntegral_univ,
      this 0 _ MeasurableSet.univ, setIntegral_univ, ht (measure_lt_top _ _)]
  · rintro f hf hfmeas heq -
    rw [integral_iUnion (fun n => hle _ (hfmeas n)) hf hg.integrableOn,
      integral_iUnion (fun n => hle _ (hfmeas n)) hf hlimint.integrableOn]
    exact tsum_congr fun n => heq _ (measure_lt_top _ _)
theorem Integrable.tendsto_eLpNorm_condexp (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    Tendsto (fun n => eLpNorm (μ[g|ℱ n] - g) 1 μ) atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condexp.mono (ℱ.le n)).aestronglyMeasurable)
    (memℒp_one_iff_integrable.2 hg) hg.uniformIntegrable_condexp_filtration.2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun n => (stronglyMeasurable_condexp.mono (ℱ.le n)).aestronglyMeasurable)
      (hg.tendsto_ae_condexp hgmeas))
@[deprecated (since := "2024-07-27")]
alias Integrable.tendsto_snorm_condexp := Integrable.tendsto_eLpNorm_condexp
theorem tendsto_ae_condexp (g : Ω → ℝ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g|ℱ n]) x) atTop (𝓝 ((μ[g|⨆ n, ℱ n]) x)) := by
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => (μ[μ[g|⨆ n, ℱ n]|ℱ n]) x) atTop (𝓝 ((μ[g|⨆ n, ℱ n]) x)) :=
    integrable_condexp.tendsto_ae_condexp stronglyMeasurable_condexp
  have heq : ∀ n, ∀ᵐ x ∂μ, (μ[μ[g|⨆ n, ℱ n]|ℱ n]) x = (μ[g|ℱ n]) x := fun n =>
    condexp_condexp_of_le (le_iSup _ n) (iSup_le fun n => ℱ.le n)
  rw [← ae_all_iff] at heq
  filter_upwards [heq, ht] with x hxeq hxt
  exact hxt.congr hxeq
theorem tendsto_eLpNorm_condexp (g : Ω → ℝ) :
    Tendsto (fun n => eLpNorm (μ[g|ℱ n] - μ[g|⨆ n, ℱ n]) 1 μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => eLpNorm (μ[μ[g|⨆ n, ℱ n]|ℱ n] - μ[g|⨆ n, ℱ n]) 1 μ) atTop (𝓝 0) :=
    integrable_condexp.tendsto_eLpNorm_condexp stronglyMeasurable_condexp
  have heq : ∀ n, ∀ᵐ x ∂μ, (μ[μ[g|⨆ n, ℱ n]|ℱ n]) x = (μ[g|ℱ n]) x := fun n =>
    condexp_condexp_of_le (le_iSup _ n) (iSup_le fun n => ℱ.le n)
  refine ht.congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [heq n] with x hxeq
  simp only [hxeq, Pi.sub_apply]
@[deprecated (since := "2024-07-27")]
alias tendsto_snorm_condexp := tendsto_eLpNorm_condexp
end L1Convergence
end MeasureTheory