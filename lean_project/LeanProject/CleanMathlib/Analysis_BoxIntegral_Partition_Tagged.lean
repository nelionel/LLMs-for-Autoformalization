import Mathlib.Analysis.BoxIntegral.Partition.Basic
noncomputable section
open Finset Function ENNReal NNReal Set
open scoped Classical
namespace BoxIntegral
variable {ι : Type*}
structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  tag : Box ι → ι → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ Box.Icc I
namespace TaggedPrepartition
variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι → ℝ}
instance : Membership (Box ι) (TaggedPrepartition I) :=
  ⟨fun π J => J ∈ π.boxes⟩
@[simp]
theorem mem_toPrepartition {π : TaggedPrepartition I} : J ∈ π.toPrepartition ↔ J ∈ π := Iff.rfl
@[simp]
theorem mem_mk (π : Prepartition I) (f h) : J ∈ mk π f h ↔ J ∈ π := Iff.rfl
def iUnion : Set (ι → ℝ) :=
  π.toPrepartition.iUnion
theorem iUnion_def : π.iUnion = ⋃ J ∈ π, ↑J := rfl
@[simp]
theorem iUnion_mk (π : Prepartition I) (f h) : (mk π f h).iUnion = π.iUnion := rfl
@[simp]
theorem iUnion_toPrepartition : π.toPrepartition.iUnion = π.iUnion := rfl
@[simp]
theorem mem_iUnion : x ∈ π.iUnion ↔ ∃ J ∈ π, x ∈ J := by
  convert Set.mem_iUnion₂
  rw [Box.mem_coe, mem_toPrepartition, exists_prop]
theorem subset_iUnion (h : J ∈ π) : ↑J ⊆ π.iUnion :=
  subset_biUnion_of_mem h
theorem iUnion_subset : π.iUnion ⊆ I :=
  iUnion₂_subset π.le_of_mem'
def IsPartition :=
  π.toPrepartition.IsPartition
theorem isPartition_iff_iUnion_eq : IsPartition π ↔ π.iUnion = I :=
  Prepartition.isPartition_iff_iUnion_eq
@[simps! (config := .asFn)]
def filter (p : Box ι → Prop) : TaggedPrepartition I :=
  ⟨π.1.filter p, π.2, π.3⟩
@[simp]
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J :=
  Finset.mem_filter
@[simp]
theorem iUnion_filter_not (π : TaggedPrepartition I) (p : Box ι → Prop) :
    (π.filter fun J => ¬p J).iUnion = π.iUnion \ (π.filter p).iUnion :=
  π.toPrepartition.iUnion_filter_not p
end TaggedPrepartition
namespace Prepartition
variable {I J : Box ι}
def biUnionTagged (π : Prepartition I) (πi : ∀ J : Box ι, TaggedPrepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.biUnion fun J => (πi J).toPrepartition
  tag J := (πi (π.biUnionIndex (fun J => (πi J).toPrepartition) J)).tag J
  tag_mem_Icc _ := Box.le_iff_Icc.1 (π.biUnionIndex_le _ _) ((πi _).tag_mem_Icc _)
@[simp]
theorem mem_biUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} :
    J ∈ π.biUnionTagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
  π.mem_biUnion
theorem tag_biUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} (hJ : J ∈ π) {J'}
    (hJ' : J' ∈ πi J) : (π.biUnionTagged πi).tag J' = (πi J).tag J' := by
  rw [← π.biUnionIndex_of_mem (πi := fun J => (πi J).toPrepartition) hJ hJ']
  rfl
@[simp]
theorem iUnion_biUnionTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) :
    (π.biUnionTagged πi).iUnion = ⋃ J ∈ π, (πi J).iUnion :=
  iUnion_biUnion _ _
theorem forall_biUnionTagged (p : (ι → ℝ) → Box ι → Prop) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (∀ J ∈ π.biUnionTagged πi, p ((π.biUnionTagged πi).tag J) J) ↔
      ∀ J ∈ π, ∀ J' ∈ πi J, p ((πi J).tag J') J' := by
  simp only [mem_biUnionTagged]
  refine ⟨fun H J hJ J' hJ' => ?_, fun H J' ⟨J, hJ, hJ'⟩ => ?_⟩
  · rw [← π.tag_biUnionTagged hJ hJ']
    exact H J' ⟨J, hJ, hJ'⟩
  · rw [π.tag_biUnionTagged hJ hJ']
    exact H J hJ J' hJ'
theorem IsPartition.biUnionTagged {π : Prepartition I} (h : IsPartition π)
    {πi : ∀ J, TaggedPrepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.biUnionTagged πi).IsPartition :=
  h.biUnion hi
end Prepartition
namespace TaggedPrepartition
variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι → ℝ}
@[simps (config := .asFn) tag]
def biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J : Box ι, Prepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.toPrepartition.biUnion πi
  tag J := π.tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _
theorem IsPartition.biUnionPrepartition {π : TaggedPrepartition I} (h : IsPartition π)
    {πi : ∀ J, Prepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.biUnionPrepartition πi).IsPartition :=
  h.biUnion hi
def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.biUnionPrepartition fun J => π'.restrict J
@[simp]
theorem infPrepartition_toPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) :
    (π.infPrepartition π').toPrepartition = π.toPrepartition ⊓ π' := rfl
theorem mem_infPrepartition_comm :
    J ∈ π₁.infPrepartition π₂.toPrepartition ↔ J ∈ π₂.infPrepartition π₁.toPrepartition := by
  simp only [← mem_toPrepartition, infPrepartition_toPrepartition, inf_comm]
theorem IsPartition.infPrepartition (h₁ : π₁.IsPartition) {π₂ : Prepartition I}
    (h₂ : π₂.IsPartition) : (π₁.infPrepartition π₂).IsPartition :=
  h₁.inf h₂
open Metric
def IsHenstock (π : TaggedPrepartition I) : Prop :=
  ∀ J ∈ π, π.tag J ∈ Box.Icc J
@[simp]
theorem isHenstock_biUnionTagged {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J} :
    IsHenstock (π.biUnionTagged πi) ↔ ∀ J ∈ π, (πi J).IsHenstock :=
  π.forall_biUnionTagged (fun x J => x ∈ Box.Icc J) πi
theorem IsHenstock.card_filter_tag_eq_le [Fintype ι] (h : π.IsHenstock) (x : ι → ℝ) :
    #{J ∈ π.boxes | π.tag J = x} ≤ 2 ^ Fintype.card ι :=
  calc
    #{J ∈ π.boxes | π.tag J = x} ≤ #{J ∈ π.boxes | x ∈ Box.Icc J} := by
      refine Finset.card_le_card fun J hJ => ?_
      rw [Finset.mem_filter] at hJ ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ ≤ 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Icc_le x
def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀ J ∈ π, Box.Icc J ⊆ closedBall (π.tag J) (r <| π.tag J)
variable {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}
@[simp]
theorem isSubordinate_biUnionTagged [Fintype ι] {π : Prepartition I}
    {πi : ∀ J, TaggedPrepartition J} :
    IsSubordinate (π.biUnionTagged πi) r ↔ ∀ J ∈ π, (πi J).IsSubordinate r :=
  π.forall_biUnionTagged (fun x J => Box.Icc J ⊆ closedBall x (r x)) πi
theorem IsSubordinate.biUnionPrepartition [Fintype ι] (h : IsSubordinate π r)
    (πi : ∀ J, Prepartition J) : IsSubordinate (π.biUnionPrepartition πi) r :=
  fun _ hJ => Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_biUnionIndex hJ) <|
    h _ <| π.toPrepartition.biUnionIndex_mem hJ
theorem IsSubordinate.infPrepartition [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I) :
    IsSubordinate (π.infPrepartition π') r :=
  h.biUnionPrepartition _
theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) : π.IsSubordinate r₂ :=
  fun _ hJ _ hx => closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)
theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ x ∈ Box.Icc I, r₁ x ≤ r₂ x) : π.IsSubordinate r₂ :=
  hr₁.mono' fun J _ => h _ <| π.tag_mem_Icc J
theorem IsSubordinate.diam_le [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r)
    (hJ : J ∈ π.boxes) : diam (Box.Icc J) ≤ 2 * r (π.tag J) :=
  calc
    diam (Box.Icc J) ≤ diam (closedBall (π.tag J) (r <| π.tag J)) :=
      diam_mono (h J hJ) isBounded_closedBall
    _ ≤ 2 * r (π.tag J) := diam_closedBall (le_of_lt (r _).2)
@[simps! (config := .asFn)]
def single (I J : Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ Box.Icc I) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun _ => x, fun _ => h⟩
@[simp]
theorem mem_single {J'} (hJ : J ≤ I) (h : x ∈ Box.Icc I) : J' ∈ single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton
instance (I : Box ι) : Inhabited (TaggedPrepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩
theorem isPartition_single_iff (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    (single I J hJ x h).IsPartition ↔ J = I :=
  Prepartition.isPartition_single_iff hJ
theorem isPartition_single (h : x ∈ Box.Icc I) : (single I I le_rfl x h).IsPartition :=
  Prepartition.isPartitionTop I
theorem forall_mem_single (p : (ι → ℝ) → Box ι → Prop) (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    (∀ J' ∈ single I J hJ x h, p ((single I J hJ x h).tag J') J') ↔ p x J := by simp
@[simp]
theorem isHenstock_single_iff (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    IsHenstock (single I J hJ x h) ↔ x ∈ Box.Icc J :=
  forall_mem_single (fun x J => x ∈ Box.Icc J) hJ h
theorem isHenstock_single (h : x ∈ Box.Icc I) : IsHenstock (single I I le_rfl x h) :=
  (isHenstock_single_iff (le_refl I) h).2 h
@[simp]
theorem isSubordinate_single [Fintype ι] (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    IsSubordinate (single I J hJ x h) r ↔ Box.Icc J ⊆ closedBall x (r x) :=
  forall_mem_single (fun x J => Box.Icc J ⊆ closedBall x (r x)) hJ h
@[simp]
theorem iUnion_single (hJ : J ≤ I) (h : x ∈ Box.Icc I) : (single I J hJ x h).iUnion = J :=
  Prepartition.iUnion_single hJ
def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) :
    TaggedPrepartition I where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  tag := π₁.boxes.piecewise π₁.tag π₂.tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]
@[simp]
theorem disjUnion_boxes (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).boxes = π₁.boxes ∪ π₂.boxes := rfl
@[simp]
theorem mem_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    J ∈ π₁.disjUnion π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
  Finset.mem_union
@[simp]
theorem iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).iUnion = π₁.iUnion ∪ π₂.iUnion :=
  Prepartition.iUnion_disjUnion h
theorem disjUnion_tag_of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J ∈ π₁) :
    (π₁.disjUnion π₂ h).tag J = π₁.tag J :=
  dif_pos hJ
theorem disjUnion_tag_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J ∈ π₂) :
    (π₁.disjUnion π₂ h).tag J = π₂.tag J :=
  dif_neg fun h₁ => h.le_bot ⟨π₁.subset_iUnion h₁ J.upper_mem, π₂.subset_iUnion hJ J.upper_mem⟩
theorem IsSubordinate.disjUnion [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsSubordinate (π₁.disjUnion π₂ h) r := by
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
theorem IsHenstock.disjUnion (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsHenstock (π₁.disjUnion π₂ h) := by
  refine fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => ?_) fun hJ => ?_
  · rw [disjUnion_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disjUnion_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
def embedBox (I J : Box ι) (h : I ≤ J) : TaggedPrepartition I ↪ TaggedPrepartition J where
  toFun π :=
    { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H
section Distortion
variable [Fintype ι] (π)
open Finset
def distortion : ℝ≥0 :=
  π.toPrepartition.distortion
theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h
theorem distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, Box.distortion J ≤ c :=
  Finset.sup_le_iff
@[simp]
theorem _root_.BoxIntegral.Prepartition.distortion_biUnionTagged (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (π.biUnionTagged πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_biUnion _ _
@[simp]
theorem distortion_biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) :
    (π.biUnionPrepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_biUnion _ _
@[simp]
theorem distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion :=
  sup_union
theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : ∀ J ∈ π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)
@[simp]
theorem distortion_single (hJ : J ≤ I) (h : x ∈ Box.Icc I) :
    distortion (single I J hJ x h) = J.distortion :=
  sup_singleton
theorem distortion_filter_le (p : Box ι → Prop) : (π.filter p).distortion ≤ π.distortion :=
  sup_mono (filter_subset _ _)
end Distortion
end TaggedPrepartition
end BoxIntegral