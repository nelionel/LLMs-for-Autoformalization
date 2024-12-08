import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Count
noncomputable section
open ProbabilityTheory
open MeasureTheory MeasurableSpace
namespace ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {s : Set Ω}
def uniformOn (s : Set Ω) : Measure Ω :=
  Measure.count[|s]
@[deprecated (since := "2024-10-09")]
noncomputable alias condCount := uniformOn
instance {s : Set Ω} : IsZeroOrProbabilityMeasure (uniformOn s) := by
  unfold uniformOn; infer_instance
@[simp]
theorem uniformOn_empty_meas : (uniformOn ∅ : Measure Ω) = 0 := by simp [uniformOn]
@[deprecated (since := "2024-10-09")]
alias condCount_empty_meas := uniformOn_empty_meas
theorem uniformOn_empty {s : Set Ω} : uniformOn s ∅ = 0 := by simp
@[deprecated (since := "2024-10-09")]
alias condCount_empty := uniformOn_empty
@[simp] lemma uniformOn_eq_zero' (hs : MeasurableSet s) : uniformOn s = 0 ↔ s.Infinite ∨ s = ∅ := by
  simp [uniformOn, hs]
@[simp] lemma uniformOn_eq_zero [MeasurableSingletonClass Ω] :
    uniformOn s = 0 ↔ s.Infinite ∨ s = ∅ := by simp [uniformOn]
theorem finite_of_uniformOn_ne_zero {s t : Set Ω} (h : uniformOn s t ≠ 0) : s.Finite := by
  by_contra hs'
  simp [uniformOn, cond, Measure.count_apply_infinite hs'] at h
@[deprecated (since := "2024-10-09")]
alias finite_of_condCount_ne_zero := finite_of_uniformOn_ne_zero
theorem uniformOn_univ [Fintype Ω] {s : Set Ω} :
    uniformOn Set.univ s = Measure.count s / Fintype.card Ω := by
  rw [uniformOn, cond_apply MeasurableSet.univ, ← ENNReal.div_eq_inv_mul, Set.univ_inter]
  congr
  rw [← Finset.coe_univ, Measure.count_apply, Finset.univ.tsum_subtype' fun _ => (1 : ENNReal)]
  · simp [Finset.card_univ]
  · exact (@Finset.coe_univ Ω _).symm ▸ MeasurableSet.univ
@[deprecated (since := "2024-10-09")]
alias condCount_univ := uniformOn_univ
variable [MeasurableSingletonClass Ω]
theorem uniformOn_isProbabilityMeasure {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty) :
    IsProbabilityMeasure (uniformOn s) := by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne
@[deprecated (since := "2024-10-09")]
alias condCount_isProbabilityMeasure := uniformOn_isProbabilityMeasure
theorem uniformOn_singleton (ω : Ω) (t : Set Ω) [Decidable (ω ∈ t)] :
    uniformOn {ω} t = if ω ∈ t then 1 else 0 := by
  rw [uniformOn, cond_apply (measurableSet_singleton ω), Measure.count_singleton, inv_one,
    one_mul]
  split_ifs
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = {ω}), Measure.count_singleton]
  · rw [(by simpa : ({ω} : Set Ω) ∩ t = ∅), Measure.count_empty]
@[deprecated (since := "2024-10-09")]
alias condCount_singleton := uniformOn_singleton
variable {s t u : Set Ω}
theorem uniformOn_inter_self (hs : s.Finite) : uniformOn s (s ∩ t) = uniformOn s t := by
  rw [uniformOn, cond_inter_self hs.measurableSet]
@[deprecated (since := "2024-10-09")]
alias condCount_inter_self := uniformOn_inter_self
theorem uniformOn_self (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s s = 1 := by
  rw [uniformOn, cond_apply hs.measurableSet, Set.inter_self, ENNReal.inv_mul_cancel]
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne
@[deprecated (since := "2024-10-09")]
alias condCount_self := uniformOn_self
theorem uniformOn_eq_one_of (hs : s.Finite) (hs' : s.Nonempty) (ht : s ⊆ t) :
    uniformOn s t = 1 := by
  haveI := uniformOn_isProbabilityMeasure hs hs'
  refine eq_of_le_of_not_lt prob_le_one ?_
  rw [not_lt, ← uniformOn_self hs hs']
  exact measure_mono ht
@[deprecated (since := "2024-10-09")]
alias condCount_eq_one_of := uniformOn_eq_one_of
theorem pred_true_of_uniformOn_eq_one (h : uniformOn s t = 1) : s ⊆ t := by
  have hsf := finite_of_uniformOn_ne_zero (by rw [h]; exact one_ne_zero)
  rw [uniformOn, cond_apply hsf.measurableSet, mul_comm] at h
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  rw [inv_inv, Measure.count_apply_finite _ hsf, Measure.count_apply_finite _ (hsf.inter_of_left _),
    Nat.cast_inj] at h
  suffices s ∩ t = s by exact this ▸ fun x hx => hx.2
  rw [← @Set.Finite.toFinset_inj _ _ _ (hsf.inter_of_left _) hsf]
  exact Finset.eq_of_subset_of_card_le (Set.Finite.toFinset_mono s.inter_subset_left) h.ge
@[deprecated (since := "2024-10-09")]
alias pred_true_of_condCount_eq_one := pred_true_of_uniformOn_eq_one
theorem uniformOn_eq_zero_iff (hs : s.Finite) : uniformOn s t = 0 ↔ s ∩ t = ∅ := by
  simp [uniformOn, cond_apply hs.measurableSet, Measure.count_apply_eq_top, Set.not_infinite.2 hs,
    Measure.count_apply_finite _ (hs.inter_of_left _)]
@[deprecated (since := "2024-10-09")]
alias condCount_eq_zero_iff := uniformOn_eq_zero_iff
theorem uniformOn_of_univ (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s Set.univ = 1 :=
  uniformOn_eq_one_of hs hs' s.subset_univ
@[deprecated (since := "2024-10-09")]
alias condCount_of_univ := uniformOn_of_univ
theorem uniformOn_inter (hs : s.Finite) :
    uniformOn s (t ∩ u) = uniformOn (s ∩ t) u * uniformOn s t := by
  by_cases hst : s ∩ t = ∅
  · rw [hst, uniformOn_empty_meas, Measure.coe_zero, Pi.zero_apply, zero_mul,
      uniformOn_eq_zero_iff hs, ← Set.inter_assoc, hst, Set.empty_inter]
  rw [uniformOn, uniformOn, cond_apply hs.measurableSet, cond_apply hs.measurableSet,
    cond_apply (hs.inter_of_left _).measurableSet, mul_comm _ (Measure.count (s ∩ t)),
    ← mul_assoc, mul_comm _ (Measure.count (s ∩ t)), ← mul_assoc, ENNReal.mul_inv_cancel, one_mul,
    mul_comm, Set.inter_assoc]
  · rwa [← Measure.count_eq_zero_iff] at hst
  · exact (Measure.count_apply_lt_top.2 <| hs.inter_of_left _).ne
@[deprecated (since := "2024-10-09")]
alias condCount_inter := uniformOn_inter
theorem uniformOn_inter' (hs : s.Finite) :
    uniformOn s (t ∩ u) = uniformOn (s ∩ u) t * uniformOn s u := by
  rw [← Set.inter_comm]
  exact uniformOn_inter hs
@[deprecated (since := "2024-10-09")]
alias condCount_inter' := uniformOn_inter'
theorem uniformOn_union (hs : s.Finite) (htu : Disjoint t u) :
    uniformOn s (t ∪ u) = uniformOn s t + uniformOn s u := by
  rw [uniformOn, cond_apply hs.measurableSet, cond_apply hs.measurableSet,
    cond_apply hs.measurableSet, Set.inter_union_distrib_left, measure_union, mul_add]
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurableSet]
@[deprecated (since := "2024-10-09")]
alias condCount_union := uniformOn_union
theorem uniformOn_compl (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty) :
    uniformOn s t + uniformOn s tᶜ = 1 := by
  rw [← uniformOn_union hs disjoint_compl_right, Set.union_compl_self,
    (uniformOn_isProbabilityMeasure hs hs').measure_univ]
@[deprecated (since := "2024-10-09")]
alias condCount_compl := uniformOn_compl
theorem uniformOn_disjoint_union (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t) :
    uniformOn s u * uniformOn (s ∪ t) s + uniformOn t u * uniformOn (s ∪ t) t =
      uniformOn (s ∪ t) u := by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  · simp
  · simp [uniformOn_self ht ht']
  · simp [uniformOn_self hs hs']
  rw [uniformOn, uniformOn, uniformOn, cond_apply hs.measurableSet,
    cond_apply ht.measurableSet, cond_apply (hs.union ht).measurableSet,
    cond_apply (hs.union ht).measurableSet, cond_apply (hs.union ht).measurableSet]
  conv_lhs =>
    rw [Set.union_inter_cancel_left, Set.union_inter_cancel_right,
      mul_comm (Measure.count (s ∪ t))⁻¹, mul_comm (Measure.count (s ∪ t))⁻¹, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Measure.count s), mul_comm _ (Measure.count t), ← mul_assoc,
      ← mul_assoc]
  rw [ENNReal.mul_inv_cancel, ENNReal.mul_inv_cancel, one_mul, one_mul, ← add_mul, ← measure_union,
    Set.union_inter_distrib_right, mul_comm]
  exacts [hst.mono inf_le_left inf_le_left, (ht.inter_of_left _).measurableSet,
    Measure.count_ne_zero ht', (Measure.count_apply_lt_top.2 ht).ne, Measure.count_ne_zero hs',
    (Measure.count_apply_lt_top.2 hs).ne]
@[deprecated (since := "2024-10-09")]
alias condCount_disjoint_union := uniformOn_disjoint_union
theorem uniformOn_add_compl_eq (u t : Set Ω) (hs : s.Finite) :
    uniformOn (s ∩ u) t * uniformOn s u + uniformOn (s ∩ uᶜ) t * uniformOn s uᶜ =
      uniformOn s t := by
  have : uniformOn s t = (uniformOn (s ∩ u) t * uniformOn (s ∩ u ∪ s ∩ uᶜ) (s ∩ u) +
      uniformOn (s ∩ uᶜ) t * uniformOn (s ∩ u ∪ s ∩ uᶜ) (s ∩ uᶜ)) := by
    rw [uniformOn_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
      (disjoint_compl_right.mono inf_le_right inf_le_right), Set.inter_union_compl]
  rw [this]
  simp [uniformOn_inter_self hs]
@[deprecated (since := "2024-10-09")]
alias condCount_add_compl_eq := uniformOn_add_compl_eq
end ProbabilityTheory