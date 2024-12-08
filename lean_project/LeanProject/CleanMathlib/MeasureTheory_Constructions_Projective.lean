import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses
open Set
namespace MeasureTheory
variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}
def IsProjectiveMeasureFamily (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  ∀ (I J : Finset ι) (hJI : J ⊆ I),
    P J = (P I).map (Finset.restrict₂ hJI)
namespace IsProjectiveMeasureFamily
variable {I J : Finset ι}
lemma eq_zero_of_isEmpty [h : IsEmpty (Π i, α i)]
    (hP : IsProjectiveMeasureFamily P) (I : Finset ι) :
    P I = 0 := by
  classical
  obtain ⟨i, hi⟩ := isEmpty_pi.mp h
  rw [hP (insert i I) I (I.subset_insert i)]
  have : IsEmpty (Π j : ↑(insert i I), α j) := by simp [hi]
  rw [(P (insert i I)).eq_zero_of_isEmpty]
  simp
lemma measure_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P) (hJI : J ⊆ I) :
    P I univ = P J univ := by
  classical
  have : (univ : Set (∀ i : I, α i)) =
      Finset.restrict₂ hJI ⁻¹' (univ : Set (∀ i : J, α i)) := by
    rw [preimage_univ]
  rw [this, ← Measure.map_apply _ MeasurableSet.univ]
  · rw [hP I J hJI]
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
lemma measure_univ_eq (hP : IsProjectiveMeasureFamily P) (I J : Finset ι) :
    P I univ = P J univ := by
  classical
  rw [← hP.measure_univ_eq_of_subset I.subset_union_left,
    ← hP.measure_univ_eq_of_subset (I.subset_union_right (s₂ := J))]
lemma congr_cylinder_of_subset (hP : IsProjectiveMeasureFamily P)
    {S : Set (∀ i : I, α i)} {T : Set (∀ i : J, α i)} (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) (hJI : J ⊆ I) :
    P I S = P J T := by
  cases isEmpty_or_nonempty (∀ i, α i) with
  | inl h =>
    suffices ∀ I, P I univ = 0 by
      simp only [Measure.measure_univ_eq_zero] at this
      simp [this]
    intro I
    simp only [isEmpty_pi] at h
    obtain ⟨i, hi_empty⟩ := h
    rw [measure_univ_eq hP I {i}]
    have : (univ : Set ((j : {x // x ∈ ({i} : Finset ι)}) → α j)) = ∅ := by simp [hi_empty]
    simp [this]
  | inr h =>
    have : S = Finset.restrict₂ hJI ⁻¹' T :=
      eq_of_cylinder_eq_of_subset h_eq hJI
    rw [hP I J hJI, Measure.map_apply _ hT, this]
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
lemma congr_cylinder (hP : IsProjectiveMeasureFamily P)
    {S : Set (∀ i : I, α i)} {T : Set (∀ i : J, α i)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) :
    P I S = P J T := by
  classical
  let U := Finset.restrict₂ Finset.subset_union_left ⁻¹' S ∩
      Finset.restrict₂ Finset.subset_union_right ⁻¹' T
  suffices P (I ∪ J) U = P I S ∧ P (I ∪ J) U = P J T from this.1.symm.trans this.2
  constructor
  · have h_eq_union : cylinder I S = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_of_subset hS h_eq_union.symm Finset.subset_union_left
  · have h_eq_union : cylinder J T = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_of_subset hT h_eq_union.symm Finset.subset_union_right
end IsProjectiveMeasureFamily
def IsProjectiveLimit (μ : Measure (∀ i, α i))
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  ∀ I : Finset ι, (μ.map I.restrict) = P I
namespace IsProjectiveLimit
variable {μ ν : Measure (∀ i, α i)}
lemma measure_cylinder (h : IsProjectiveLimit μ P)
    (I : Finset ι) {s : Set (∀ i : I, α i)} (hs : MeasurableSet s) :
    μ (cylinder I s) = P I s := by
  rw [cylinder, ← Measure.map_apply _ hs, h I]
  exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
lemma measure_univ_eq (hμ : IsProjectiveLimit μ P) (I : Finset ι) :
    μ univ = P I univ := by
  rw [← cylinder_univ I, hμ.measure_cylinder _ MeasurableSet.univ]
lemma isFiniteMeasure [∀ i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P) :
    IsFiniteMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_lt_top _ _
lemma isProbabilityMeasure [∀ i, IsProbabilityMeasure (P i)] (hμ : IsProjectiveLimit μ P) :
    IsProbabilityMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_univ
lemma measure_univ_unique (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ univ = ν univ := by
  rw [hμ.measure_univ_eq (∅ : Finset ι), hν.measure_univ_eq (∅ : Finset ι)]
theorem unique [∀ i, IsFiniteMeasure (P i)]
    (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ = ν := by
  haveI : IsFiniteMeasure μ := hμ.isFiniteMeasure
  refine ext_of_generate_finite (measurableCylinders α) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs ↦ ?_) (hμ.measure_univ_unique hν)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [hμ.measure_cylinder _ hS, hν.measure_cylinder _ hS]
end IsProjectiveLimit
end MeasureTheory