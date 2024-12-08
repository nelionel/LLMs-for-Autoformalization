import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
noncomputable section
open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap
open scoped NNReal ENNReal Topology MeasureTheory
namespace MeasureTheory
variable {α E : Type*} {m m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {f : α → E} {s : Set α}
theorem condexp_ae_eq_restrict_zero (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict s] 0) :
    μ[f|m] =ᵐ[μ.restrict s] 0 := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; rfl
  haveI : SigmaFinite (μ.trim hm) := hμm
  have : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    exact Restrict.sigmaFinite _ s
  by_cases hf_int : Integrable f μ
  swap; · rw [condexp_undef hf_int]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm ?_ ?_ ?_ ?_ ?_
  · exact fun t _ _ => integrable_condexp.integrableOn.integrableOn
  · exact fun t _ _ => (integrable_zero _ _ _).integrableOn
  · intro t ht _
    rw [Measure.restrict_restrict (hm _ ht), setIntegral_condexp hm hf_int (ht.inter hs), ←
      Measure.restrict_restrict (hm _ ht)]
    refine setIntegral_congr_ae (hm _ ht) ?_
    filter_upwards [hf] with x hx _ using hx
  · exact stronglyMeasurable_condexp.aeStronglyMeasurable'
  · exact stronglyMeasurable_zero.aeStronglyMeasurable'
theorem condexp_indicator_aux (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    μ[s.indicator f|m] =ᵐ[μ] s.indicator (μ[f|m]) := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm, Set.indicator_zero']; rfl
  have hsf_zero : ∀ g : α → E, g =ᵐ[μ.restrict sᶜ] 0 → s.indicator g =ᵐ[μ] g := fun g =>
    indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs)
  refine ((hsf_zero (μ[f|m]) (condexp_ae_eq_restrict_zero hs.compl hf)).trans ?_).symm
  exact condexp_congr_ae (hsf_zero f hf).symm
theorem condexp_indicator (hf_int : Integrable f μ) (hs : MeasurableSet[m] s) :
    μ[s.indicator f|m] =ᵐ[μ] s.indicator (μ[f|m]) := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm, Set.indicator_zero']; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm, Set.indicator_zero']; rfl
  haveI : SigmaFinite (μ.trim hm) := hμm
  have : s.indicator (μ[f|m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f|m]) := by
    rw [Set.indicator_self_add_compl s f]
  refine (this.trans ?_).symm
  calc
    s.indicator (μ[s.indicator f + sᶜ.indicator f|m]) =ᵐ[μ]
        s.indicator (μ[s.indicator f|m] + μ[sᶜ.indicator f|m]) := by
      have : μ[s.indicator f + sᶜ.indicator f|m] =ᵐ[μ] μ[s.indicator f|m] + μ[sᶜ.indicator f|m] :=
        condexp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl))
      filter_upwards [this] with x hx
      classical rw [Set.indicator_apply, Set.indicator_apply, hx]
    _ = s.indicator (μ[s.indicator f|m]) + s.indicator (μ[sᶜ.indicator f|m]) :=
      (s.indicator_add' _ _)
    _ =ᵐ[μ] s.indicator (μ[s.indicator f|m]) +
        s.indicator (sᶜ.indicator (μ[sᶜ.indicator f|m])) := by
      refine Filter.EventuallyEq.rfl.add ?_
      have : sᶜ.indicator (μ[sᶜ.indicator f|m]) =ᵐ[μ] μ[sᶜ.indicator f|m] := by
        refine (condexp_indicator_aux hs.compl ?_).symm.trans ?_
        · exact indicator_ae_eq_restrict_compl (hm _ hs.compl)
        · rw [Set.indicator_indicator, Set.inter_self]
      filter_upwards [this] with x hx
      by_cases hxs : x ∈ s
      · simp only [hx, hxs, Set.indicator_of_mem]
      · simp only [hxs, Set.indicator_of_not_mem, not_false_iff]
    _ =ᵐ[μ] s.indicator (μ[s.indicator f|m]) := by
      rw [Set.indicator_indicator, Set.inter_compl_self, Set.indicator_empty', add_zero]
    _ =ᵐ[μ] μ[s.indicator f|m] := by
      refine (condexp_indicator_aux hs ?_).symm.trans ?_
      · exact indicator_ae_eq_restrict_compl (hm _ hs)
      · rw [Set.indicator_indicator, Set.inter_self]
theorem condexp_restrict_ae_eq_restrict (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs_m : MeasurableSet[m] s) (hf_int : Integrable f μ) :
    (μ.restrict s)[f|m] =ᵐ[μ.restrict s] μ[f|m] := by
  have : SigmaFinite ((μ.restrict s).trim hm) := by rw [← restrict_trim hm _ hs_m]; infer_instance
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  refine EventuallyEq.trans ?_ (condexp_indicator hf_int hs_m)
  refine ae_eq_condexp_of_forall_setIntegral_eq hm (hf_int.indicator (hm _ hs_m)) ?_ ?_ ?_
  · intro t ht _
    rw [← integrable_indicator_iff (hm _ ht), Set.indicator_indicator, Set.inter_comm, ←
      Set.indicator_indicator]
    suffices h_int_restrict : Integrable (t.indicator ((μ.restrict s)[f|m])) (μ.restrict s) by
      rw [integrable_indicator_iff (hm _ hs_m), IntegrableOn]
      rw [integrable_indicator_iff (hm _ ht), IntegrableOn] at h_int_restrict ⊢
      exact h_int_restrict
    exact integrable_condexp.indicator (hm _ ht)
  · intro t ht _
    calc
      ∫ x in t, s.indicator ((μ.restrict s)[f|m]) x ∂μ =
          ∫ x in t, ((μ.restrict s)[f|m]) x ∂μ.restrict s := by
        rw [integral_indicator (hm _ hs_m), Measure.restrict_restrict (hm _ hs_m),
          Measure.restrict_restrict (hm _ ht), Set.inter_comm]
      _ = ∫ x in t, f x ∂μ.restrict s := setIntegral_condexp hm hf_int.integrableOn ht
      _ = ∫ x in t, s.indicator f x ∂μ := by
        rw [integral_indicator (hm _ hs_m), Measure.restrict_restrict (hm _ hs_m),
          Measure.restrict_restrict (hm _ ht), Set.inter_comm]
  · exact (stronglyMeasurable_condexp.indicator hs_m).aeStronglyMeasurable'
theorem condexp_ae_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm)]
    [SigmaFinite (μ.trim hm₂)] (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) ↔ MeasurableSet[m₂] (s ∩ t)) :
    μ[f|m] =ᵐ[μ.restrict s] μ[f|m₂] := by
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  have hs_m₂ : MeasurableSet[m₂] s := by rwa [← Set.inter_univ s, ← hs Set.univ, Set.inter_univ]
  by_cases hf_int : Integrable f μ
  swap; · simp_rw [condexp_undef hf_int]; rfl
  refine ((condexp_indicator hf_int hs_m).symm.trans ?_).trans (condexp_indicator hf_int hs_m₂)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm₂
    (fun s _ _ => integrable_condexp.integrableOn)
    (fun s _ _ => integrable_condexp.integrableOn) ?_ ?_
    stronglyMeasurable_condexp.aeStronglyMeasurable'
  swap
  · have : StronglyMeasurable[m] (μ[s.indicator f|m]) := stronglyMeasurable_condexp
    refine this.aeStronglyMeasurable'.aeStronglyMeasurable'_of_measurableSpace_le_on hm hs_m
      (fun t => (hs t).mp) ?_
    exact condexp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m))
  intro t ht _
  have : ∫ x in t, (μ[s.indicator f|m]) x ∂μ = ∫ x in s ∩ t, (μ[s.indicator f|m]) x ∂μ := by
    rw [← integral_add_compl (hm _ hs_m) integrable_condexp.integrableOn]
    suffices ∫ x in sᶜ, (μ[s.indicator f|m]) x ∂μ.restrict t = 0 by
      rw [this, add_zero, Measure.restrict_restrict (hm _ hs_m)]
    rw [Measure.restrict_restrict (MeasurableSet.compl (hm _ hs_m))]
    suffices μ[s.indicator f|m] =ᵐ[μ.restrict sᶜ] 0 by
      rw [Set.inter_comm, ← Measure.restrict_restrict (hm₂ _ ht)]
      calc
        ∫ x : α in t, (μ[s.indicator f|m]) x ∂μ.restrict sᶜ =
            ∫ x : α in t, 0 ∂μ.restrict sᶜ := by
          refine setIntegral_congr_ae (hm₂ _ ht) ?_
          filter_upwards [this] with x hx _ using hx
        _ = 0 := integral_zero _ _
    refine condexp_ae_eq_restrict_zero hs_m.compl ?_
    exact indicator_ae_eq_restrict_compl (hm _ hs_m)
  have hst_m : MeasurableSet[m] (s ∩ t) := (hs _).mpr (hs_m₂.inter ht)
  simp_rw [this, setIntegral_condexp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    setIntegral_condexp hm (hf_int.indicator (hm _ hs_m)) hst_m, integral_indicator (hm _ hs_m),
    Measure.restrict_restrict (hm _ hs_m), ← Set.inter_assoc, Set.inter_self]
end MeasureTheory