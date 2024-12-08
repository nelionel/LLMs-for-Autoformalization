import Mathlib.Analysis.BoxIntegral.Box.SubboxInduction
import Mathlib.Analysis.BoxIntegral.Partition.Tagged
namespace BoxIntegral
open Set Metric
open scoped Classical
open Topology
noncomputable section
variable {ι : Type*} [Fintype ι] {I J : Box ι}
namespace Prepartition
def splitCenter (I : Box ι) : Prepartition I where
  boxes := Finset.univ.map (Box.splitCenterBoxEmb I)
  le_of_mem' := by simp [I.splitCenterBox_le]
  pairwiseDisjoint := by
    rw [Finset.coe_map, Finset.coe_univ, image_univ]
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne
    exact I.disjoint_splitCenterBox (mt (congr_arg _) Hne)
@[simp]
theorem mem_splitCenter : J ∈ splitCenter I ↔ ∃ s, I.splitCenterBox s = J := by simp [splitCenter]
theorem isPartition_splitCenter (I : Box ι) : IsPartition (splitCenter I) := fun x hx => by
  simp [hx]
theorem upper_sub_lower_of_mem_splitCenter (h : J ∈ splitCenter I) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
  let ⟨s, hs⟩ := mem_splitCenter.1 h
  hs ▸ I.upper_sub_lower_splitCenterBox s i
end Prepartition
namespace Box
open Prepartition TaggedPrepartition
@[elab_as_elim]
theorem subbox_induction_on {p : Box ι → Prop} (I : Box ι)
    (H_ind : ∀ J ≤ I, (∀ J' ∈ splitCenter J, p J') → p J)
    (H_nhds : ∀ z ∈ Box.Icc I, ∃ U ∈ 𝓝[Box.Icc I] z, ∀ J ≤ I, ∀ (m : ℕ),
      z ∈ Box.Icc J → Box.Icc J ⊆ U →
        (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) → p J) :
    p I := by
  refine subbox_induction_on' I (fun J hle hs => H_ind J hle fun J' h' => ?_) H_nhds
  rcases mem_splitCenter.1 h' with ⟨s, rfl⟩
  exact hs s
theorem exists_taggedPartition_isHenstock_isSubordinate_homothetic (I : Box ι)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π : TaggedPrepartition I, π.IsPartition ∧ π.IsHenstock ∧ π.IsSubordinate r ∧
      (∀ J ∈ π, ∃ m : ℕ, ∀ i, (J : _).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) ∧
        π.distortion = I.distortion := by
  refine subbox_induction_on I (fun J _ hJ => ?_) fun z _ => ?_
  · choose! πi hP hHen hr Hn _ using hJ
    choose! n hn using Hn
    have hP : ((splitCenter J).biUnionTagged πi).IsPartition :=
      (isPartition_splitCenter _).biUnionTagged hP
    have hsub : ∀ J' ∈ (splitCenter J).biUnionTagged πi, ∃ n : ℕ, ∀ i,
        (J' : _).upper i - J'.lower i = (J.upper i - J.lower i) / 2 ^ n := by
      intro J' hJ'
      rcases (splitCenter J).mem_biUnionTagged.1 hJ' with ⟨J₁, h₁, h₂⟩
      refine ⟨n J₁ J' + 1, fun i => ?_⟩
      simp only [hn J₁ h₁ J' h₂, upper_sub_lower_of_mem_splitCenter h₁, pow_succ', div_div]
    refine ⟨_, hP, isHenstock_biUnionTagged.2 hHen, isSubordinate_biUnionTagged.2 hr, hsub, ?_⟩
    refine TaggedPrepartition.distortion_of_const _ hP.nonempty_boxes fun J' h' => ?_
    rcases hsub J' h' with ⟨n, hn⟩
    exact Box.distortion_eq_of_sub_eq_div hn
  · refine ⟨Box.Icc I ∩ closedBall z (r z),
      inter_mem_nhdsWithin _ (closedBall_mem_nhds _ (r z).coe_prop), ?_⟩
    intro J _ n Hmem HIcc Hsub
    rw [Set.subset_inter_iff] at HIcc
    refine ⟨single _ _ le_rfl _ Hmem, isPartition_single _, isHenstock_single _,
      (isSubordinate_single _ _).2 HIcc.2, ?_, distortion_single _ _⟩
    simp only [TaggedPrepartition.mem_single, forall_eq]
    refine ⟨0, fun i => ?_⟩
    simp
end Box
namespace Prepartition
open TaggedPrepartition Finset Function
theorem exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : Prepartition I) :
    ∃ π' : TaggedPrepartition I, π'.toPrepartition ≤ π ∧ π'.IsHenstock ∧ π'.IsSubordinate r ∧
      π'.distortion = π.distortion ∧ π'.iUnion = π.iUnion := by
  have := fun J => Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic J r
  choose! πi πip πiH πir _ πid using this
  refine ⟨π.biUnionTagged πi, biUnion_le _ _, isHenstock_biUnionTagged.2 fun J _ => πiH J,
    isSubordinate_biUnionTagged.2 fun J _ => πir J, ?_, π.iUnion_biUnion_partition fun J _ => πip J⟩
  rw [distortion_biUnionTagged]
  exact sup_congr rfl fun J _ => πid J
def toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose
theorem toSubordinate_toPrepartition_le (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).toPrepartition ≤ π :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.1
theorem isHenstock_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsHenstock :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.1
theorem isSubordinate_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsSubordinate r :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.1
@[simp]
theorem distortion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).distortion = π.distortion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.1
@[simp]
theorem iUnion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).iUnion = π.iUnion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.2
end Prepartition
namespace TaggedPrepartition
def unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  π₁.disjUnion (π₂.toSubordinate r)
    (((π₂.iUnion_toSubordinate r).trans hU).symm ▸ disjoint_sdiff_self_right)
theorem isPartition_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    IsPartition (π₁.unionComplToSubordinate π₂ hU r) :=
  Prepartition.isPartitionDisjUnionOfEqDiff ((π₂.iUnion_toSubordinate r).trans hU)
@[simp]
theorem unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).boxes = π₁.boxes ∪ (π₂.toSubordinate r).boxes := rfl
@[simp]
theorem iUnion_unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).iUnion = I :=
  (isPartition_unionComplToSubordinate _ _ _ _).iUnion_eq
@[simp]
theorem distortion_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).distortion = max π₁.distortion π₂.distortion := by
  simp [unionComplToSubordinate]
end TaggedPrepartition
end
end BoxIntegral