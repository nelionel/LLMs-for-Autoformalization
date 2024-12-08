import Mathlib.MeasureTheory.Measure.Typeclasses
noncomputable section
open ENNReal MeasureTheory MeasureTheory.Measure MeasurableSpace Set
variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}
namespace ProbabilityTheory
variable (μ) in
def cond (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s
@[inherit_doc] scoped notation:max μ "[|" s "]" => ProbabilityTheory.cond μ s
@[inherit_doc cond] scoped notation3:max μ "[" t " | " s "]" => ProbabilityTheory.cond μ s t
scoped notation:max μ "[|" X " in " s "]" => μ[|X ⁻¹' s]
scoped notation:max μ "[" s " | "  X " in " t "]" => μ[s | X ⁻¹' t]
scoped notation:max μ "[|" X " ← " x "]" => μ[|X in {x}]
scoped notation:max μ "[" s " | "  X " ← " x "]" => μ[s | X in {x}]
theorem cond_isProbabilityMeasure_of_finite (hcs : μ s ≠ 0) (hs : μ s ≠ ∞) :
    IsProbabilityMeasure μ[|s] :=
  ⟨by
    unfold ProbabilityTheory.cond
    simp only [Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hcs hs⟩
theorem cond_isProbabilityMeasure [IsFiniteMeasure μ] (hcs : μ s ≠ 0) :
    IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure_of_finite hcs (measure_ne_top μ s)
instance : IsZeroOrProbabilityMeasure μ[|s] := by
  constructor
  simp only [cond, Measure.coe_smul, Pi.smul_apply, MeasurableSet.univ, Measure.restrict_apply,
    univ_inter, smul_eq_mul, ← ENNReal.div_eq_inv_mul]
  rcases eq_or_ne (μ s) 0 with h | h
  · simp [h]
  rcases eq_or_ne (μ s) ∞ with h' | h'
  · simp [h']
  simp [ENNReal.div_self h h']
variable (μ) in
theorem cond_toMeasurable_eq :
    μ[|(toMeasurable μ s)] = μ[|s] := by
  unfold cond
  by_cases hnt : μ s = ∞
  · simp [hnt]
  · simp [Measure.restrict_toMeasurable hnt]
lemma cond_absolutelyContinuous : μ[|s] ≪ μ :=
  smul_absolutelyContinuous.trans restrict_le_self.absolutelyContinuous
lemma absolutelyContinuous_cond_univ [IsFiniteMeasure μ] : μ ≪ μ[|univ] := by
  rw [cond, restrict_univ]
  refine absolutelyContinuous_smul ?_
  simp [measure_ne_top]
section Bayes
variable (μ) in
@[simp] lemma cond_empty : μ[|∅] = 0 := by simp [cond]
variable (μ) in
@[simp] lemma cond_univ [IsProbabilityMeasure μ] : μ[|Set.univ] = μ := by
  simp [cond, measure_univ, Measure.restrict_univ]
@[simp] lemma cond_eq_zero : μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0 := by simp [cond]
lemma cond_eq_zero_of_meas_eq_zero (hμs : μ s = 0) : μ[|s] = 0 := by simp [hμs]
theorem cond_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply' hms, Set.inter_comm, smul_eq_mul]
theorem cond_apply' (ht : MeasurableSet t) (μ : Measure Ω) : μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply ht, Set.inter_comm, smul_eq_mul]
@[simp] lemma cond_apply_self (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : μ[s|s] = 1 := by
  simpa [cond] using ENNReal.inv_mul_cancel hs₀ hs
theorem cond_inter_self (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) :
    μ[s ∩ t|s] = μ[t|s] := by
  rw [cond_apply hms, ← Set.inter_assoc, Set.inter_self, ← cond_apply hms]
theorem inter_pos_of_cond_ne_zero (hms : MeasurableSet s) (hcst : μ[t|s] ≠ 0) : 0 < μ (s ∩ t) := by
  refine pos_iff_ne_zero.mpr (right_ne_zero_of_mul (a := (μ s)⁻¹) ?_)
  convert hcst
  simp [hms, Set.inter_comm, cond]
lemma cond_pos_of_inter_ne_zero [IsFiniteMeasure μ] (hms : MeasurableSet s) (hci : μ (s ∩ t) ≠ 0) :
    0 < μ[t | s] := by
  rw [cond_apply hms]
  refine ENNReal.mul_pos ?_ hci
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
lemma cond_cond_eq_cond_inter' (hms : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s ≠ ∞) :
    μ[|s][|t] = μ[|s ∩ t] := by
  ext u
  rw [cond_apply hmt, cond_apply hms, cond_apply hms, cond_apply (hms.inter hmt)]
  obtain hst | hst := eq_or_ne (μ (s ∩ t)) 0
  · have : μ (s ∩ t ∩ u) = 0 := measure_mono_null Set.inter_subset_left hst
    simp [this, ← Set.inter_assoc]
  · have hcs' : μ s ≠ 0 :=
      (measure_pos_of_superset Set.inter_subset_left hst).ne'
    simp [*, ← mul_assoc, ← Set.inter_assoc, ENNReal.mul_inv, ENNReal.mul_inv_cancel,
      mul_right_comm _ _ (μ s)⁻¹]
theorem cond_cond_eq_cond_inter (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[|s][|t] = μ[|s ∩ t] :=
  cond_cond_eq_cond_inter' hms hmt (measure_ne_top μ s)
theorem cond_mul_eq_inter' (hms : MeasurableSet s) (hcs' : μ s ≠ ∞) (t : Set Ω) :
    μ[t|s] * μ s = μ (s ∩ t) := by
  obtain hcs | hcs := eq_or_ne (μ s) 0
  · simp [hcs, measure_inter_null_of_null_left]
  · rw [cond_apply hms, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hcs hcs', one_mul]
theorem cond_mul_eq_inter (hms : MeasurableSet s) (t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t|s] * μ s = μ (s ∩ t) := cond_mul_eq_inter' hms (measure_ne_top _ s) t
theorem cond_add_cond_compl_eq (hms : MeasurableSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t|s] * μ s + μ[t|sᶜ] * μ sᶜ = μ t := by
  rw [cond_mul_eq_inter hms, cond_mul_eq_inter hms.compl, Set.inter_comm _ t,
    Set.inter_comm _ t]
  exact measure_inter_add_diff t hms
theorem cond_eq_inv_mul_cond_mul (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t := by
  rw [mul_assoc, cond_mul_eq_inter hmt s, Set.inter_comm, cond_apply hms]
end Bayes
lemma comap_cond {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ ω ∂μ, ω ∈ range i)
    (hs : MeasurableSet s) : comap i μ[|s] = (comap i μ)[|i in s] := by
  ext t ht
  change μ (range i)ᶜ = 0 at hi'
  rw [cond_apply, comap_apply, cond_apply, comap_apply, comap_apply, image_inter,
    image_preimage_eq_inter_range, inter_right_comm, measure_inter_conull hi',
    measure_inter_conull hi']
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hs
  | exact ht
  | exact hi.measurable hs
  | exact (hi.measurable hs).inter ht
variable [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
lemma sum_meas_smul_cond_fiber {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by
  ext E hE
  calc
    _ = ∑ x, μ (X ⁻¹' {x} ∩ E) := by
      simp only [Measure.coe_finset_sum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x ∈ Finset.univ, X ⁻¹' {x} ∩ E = E := by ext; simp
      rw [← measure_biUnion_finset _ fun _ _ ↦ (hX (.singleton _)).inter hE, this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])
end ProbabilityTheory