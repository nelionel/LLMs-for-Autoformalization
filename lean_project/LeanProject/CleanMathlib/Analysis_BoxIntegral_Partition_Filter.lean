import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.Analysis.BoxIntegral.Partition.Split
open Set Function Filter Metric Finset Bool
open scoped Classical Topology Filter NNReal
noncomputable section
namespace BoxIntegral
variable {ι : Type*} [Fintype ι] {I J : Box ι} {c c₁ c₂ : ℝ≥0}
open TaggedPrepartition
@[ext]
structure IntegrationParams : Type where
  (bRiemann bHenstock bDistortion : Bool)
variable {l l₁ l₂ : IntegrationParams}
namespace IntegrationParams
def equivProd : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ where
  toFun l := ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance : PartialOrder IntegrationParams :=
  PartialOrder.lift equivProd equivProd.injective
def isoProd : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ :=
  ⟨equivProd, Iff.rfl⟩
instance : BoundedOrder IntegrationParams :=
  isoProd.symm.toGaloisInsertion.liftBoundedOrder
instance : Inhabited IntegrationParams :=
  ⟨⊥⟩
instance : DecidableRel ((· ≤ ·) : IntegrationParams → IntegrationParams → Prop) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableEq IntegrationParams :=
  fun _ _ => decidable_of_iff _ IntegrationParams.ext_iff.symm
def Riemann : IntegrationParams where
  bRiemann := true
  bHenstock := true
  bDistortion := false
def Henstock : IntegrationParams :=
  ⟨false, true, false⟩
def McShane : IntegrationParams :=
  ⟨false, false, false⟩
def GP : IntegrationParams := ⊥
theorem henstock_le_riemann : Henstock ≤ Riemann := by trivial
theorem henstock_le_mcShane : Henstock ≤ McShane := by trivial
theorem gp_le : GP ≤ l :=
  bot_le
structure MemBaseSet (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : TaggedPrepartition I) : Prop where
  protected isSubordinate : π.IsSubordinate r
  protected isHenstock : l.bHenstock → π.IsHenstock
  protected distortion_le : l.bDistortion → π.distortion ≤ c
  protected exists_compl : l.bDistortion → ∃ π' : Prepartition I,
    π'.iUnion = ↑I \ π.iUnion ∧ π'.distortion ≤ c
def RCond {ι : Type*} (l : IntegrationParams) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  l.bRiemann → ∀ x, r x = r 0
def toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    Filter (TaggedPrepartition I) :=
  ⨅ (r : (ι → ℝ) → Ioi (0 : ℝ)) (_ : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }
def toFilter (l : IntegrationParams) (I : Box ι) : Filter (TaggedPrepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortion I c
def toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (π₀ : Prepartition I) :=
  l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }
def toFilteriUnion (I : Box ι) (π₀ : Prepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortioniUnion I c π₀
theorem rCond_of_bRiemann_eq_false {ι} (l : IntegrationParams) (hl : l.bRiemann = false)
    {r : (ι → ℝ) → Ioi (0 : ℝ)} : l.RCond r := by
  simp [RCond, hl]
theorem toFilter_inf_iUnion_eq (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    l.toFilter I ⊓ 𝓟 { π | π.iUnion = π₀.iUnion } = l.toFilteriUnion I π₀ :=
  (iSup_inf_principal _ _).symm
variable {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} {π π₁ π₂ : TaggedPrepartition I}
variable (I) in
theorem MemBaseSet.mono' (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
    (hr : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) (hπ : l₁.MemBaseSet I c₁ r₁ π) :
    l₂.MemBaseSet I c₂ r₂ π :=
  ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂),
    fun hD => (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
    fun hD => (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp fun _ hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩
variable (I) in
@[mono]
theorem MemBaseSet.mono (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
    (hr : ∀ x ∈ Box.Icc I, r₁ x ≤ r₂ x) (hπ : l₁.MemBaseSet I c₁ r₁ π) : l₂.MemBaseSet I c₂ r₂ π :=
  hπ.mono' I h hc fun J _ => hr _ <| π.tag_mem_Icc J
theorem MemBaseSet.exists_common_compl
    (h₁ : l.MemBaseSet I c₁ r₁ π₁) (h₂ : l.MemBaseSet I c₂ r₂ π₂)
    (hU : π₁.iUnion = π₂.iUnion) :
    ∃ π : Prepartition I, π.iUnion = ↑I \ π₁.iUnion ∧
      (l.bDistortion → π.distortion ≤ c₁) ∧ (l.bDistortion → π.distortion ≤ c₂) := by
  wlog hc : c₁ ≤ c₂ with H
  · simpa [hU, _root_.and_comm] using
      @H _ _ I c₂ c₁ l r₂ r₁ π₂ π₁ h₂ h₁ hU.symm (le_of_not_le hc)
  by_cases hD : (l.bDistortion : Prop)
  · rcases h₁.4 hD with ⟨π, hπU, hπc⟩
    exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
  · exact ⟨π₁.toPrepartition.compl, π₁.toPrepartition.iUnion_compl,
      fun h => (hD h).elim, fun h => (hD h).elim⟩
protected theorem MemBaseSet.unionComplToSubordinate (hπ₁ : l.MemBaseSet I c r₁ π₁)
    (hle : ∀ x ∈ Box.Icc I, r₂ x ≤ r₁ x) {π₂ : Prepartition I} (hU : π₂.iUnion = ↑I \ π₁.iUnion)
    (hc : l.bDistortion → π₂.distortion ≤ c) :
    l.MemBaseSet I c r₁ (π₁.unionComplToSubordinate π₂ hU r₂) :=
  ⟨hπ₁.1.disjUnion ((π₂.isSubordinate_toSubordinate r₂).mono hle) _,
    fun h => (hπ₁.2 h).disjUnion (π₂.isHenstock_toSubordinate _) _,
    fun h => (distortion_unionComplToSubordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)),
    fun _ => ⟨⊥, by simp⟩⟩
variable {r : (ι → ℝ) → Ioi (0 : ℝ)}
protected theorem MemBaseSet.filter (hπ : l.MemBaseSet I c r π) (p : Box ι → Prop) :
    l.MemBaseSet I c r (π.filter p) := by
  refine ⟨fun J hJ => hπ.1 J (π.mem_filter.1 hJ).1, fun hH J hJ => hπ.2 hH J (π.mem_filter.1 hJ).1,
    fun hD => (distortion_filter_le _ _).trans (hπ.3 hD), fun hD => ?_⟩
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩
  set π₂ := π.filter fun J => ¬p J
  have : Disjoint π₁.iUnion π₂.iUnion := by
    simpa [π₂, hπ₁U] using disjoint_sdiff_self_left.mono_right sdiff_le
  refine ⟨π₁.disjUnion π₂.toPrepartition this, ?_, ?_⟩
  · suffices ↑I \ π.iUnion ∪ π.iUnion \ (π.filter p).iUnion = ↑I \ (π.filter p).iUnion by
      simp [π₂, *]
    have h : (π.filter p).iUnion ⊆ π.iUnion :=
      biUnion_subset_biUnion_left (Finset.filter_subset _ _)
    ext x
    fconstructor
    · rintro (⟨hxI, hxπ⟩ | ⟨hxπ, hxp⟩)
      exacts [⟨hxI, mt (@h x) hxπ⟩, ⟨π.iUnion_subset hxπ, hxp⟩]
    · rintro ⟨hxI, hxp⟩
      by_cases hxπ : x ∈ π.iUnion
      exacts [Or.inr ⟨hxπ, hxp⟩, Or.inl ⟨hxI, hxπ⟩]
  · have : (π.filter fun J => ¬p J).distortion ≤ c := (distortion_filter_le _ _).trans (hπ.3 hD)
    simpa [hc]
theorem biUnionTagged_memBaseSet {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J}
    (h : ∀ J ∈ π, l.MemBaseSet J c r (πi J)) (hp : ∀ J ∈ π, (πi J).IsPartition)
    (hc : l.bDistortion → π.compl.distortion ≤ c) : l.MemBaseSet I c r (π.biUnionTagged πi) := by
  refine ⟨TaggedPrepartition.isSubordinate_biUnionTagged.2 fun J hJ => (h J hJ).1,
    fun hH => TaggedPrepartition.isHenstock_biUnionTagged.2 fun J hJ => (h J hJ).2 hH,
    fun hD => ?_, fun hD => ?_⟩
  · rw [Prepartition.distortion_biUnionTagged, Finset.sup_le_iff]
    exact fun J hJ => (h J hJ).3 hD
  · refine ⟨_, ?_, hc hD⟩
    rw [π.iUnion_compl, ← π.iUnion_biUnion_partition hp]
    rfl
@[mono]
theorem RCond.mono {ι : Type*} {r : (ι → ℝ) → Ioi (0 : ℝ)} (h : l₁ ≤ l₂) (hr : l₂.RCond r) :
    l₁.RCond r :=
  fun hR => hr (le_iff_imp.1 h.1 hR)
nonrec theorem RCond.min {ι : Type*} {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} (h₁ : l.RCond r₁)
    (h₂ : l.RCond r₂) : l.RCond fun x => min (r₁ x) (r₂ x) :=
  fun hR x => congr_arg₂ min (h₁ hR x) (h₂ hR x)
@[mono]
theorem toFilterDistortion_mono (I : Box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) :
    l₁.toFilterDistortion I c₁ ≤ l₂.toFilterDistortion I c₂ :=
  iInf_mono fun _ =>
    iInf_mono' fun hr =>
      ⟨hr.mono h, principal_mono.2 fun _ => MemBaseSet.mono I h hc fun _ _ => le_rfl⟩
@[mono]
theorem toFilter_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂) :
    l₁.toFilter I ≤ l₂.toFilter I :=
  iSup_mono fun _ => toFilterDistortion_mono I h le_rfl
@[mono]
theorem toFilteriUnion_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂)
    (π₀ : Prepartition I) : l₁.toFilteriUnion I π₀ ≤ l₂.toFilteriUnion I π₀ :=
  iSup_mono fun _ => inf_le_inf_right _ <| toFilterDistortion_mono _ h le_rfl
theorem toFilteriUnion_congr (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : l.toFilteriUnion I π₁ = l.toFilteriUnion I π₂ := by
  simp only [toFilteriUnion, toFilterDistortioniUnion, h]
theorem hasBasis_toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    (l.toFilterDistortion I c).HasBasis l.RCond fun r => { π | l.MemBaseSet I c r π } :=
  hasBasis_biInf_principal'
    (fun _ hr₁ _ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_left _ _,
        fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_right _ _⟩)
    ⟨fun _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩, fun _ _ => rfl⟩
theorem hasBasis_toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0)
    (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I c π₀).HasBasis l.RCond fun r =>
      { π | l.MemBaseSet I c r π ∧ π.iUnion = π₀.iUnion } :=
  (l.hasBasis_toFilterDistortion I c).inf_principal _
theorem hasBasis_toFilteriUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.iUnion = π₀.iUnion } := by
  have := fun c => l.hasBasis_toFilterDistortioniUnion I c π₀
  simpa only [setOf_and, setOf_exists] using hasBasis_iSup this
theorem hasBasis_toFilteriUnion_top (l : IntegrationParams) (I : Box ι) :
    (l.toFilteriUnion I ⊤).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.IsPartition } := by
  simpa only [TaggedPrepartition.isPartition_iff_iUnion_eq, Prepartition.iUnion_top] using
    l.hasBasis_toFilteriUnion I ⊤
theorem hasBasis_toFilter (l : IntegrationParams) (I : Box ι) :
    (l.toFilter I).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π } := by
  simpa only [setOf_exists] using hasBasis_iSup (l.hasBasis_toFilterDistortion I)
theorem tendsto_embedBox_toFilteriUnion_top (l : IntegrationParams) (h : I ≤ J) :
    Tendsto (TaggedPrepartition.embedBox I J h) (l.toFilteriUnion I ⊤)
      (l.toFilteriUnion J (Prepartition.single J I h)) := by
  simp only [toFilteriUnion, tendsto_iSup]; intro c
  set π₀ := Prepartition.single J I h
  refine le_iSup_of_le (max c π₀.compl.distortion) ?_
  refine ((l.hasBasis_toFilterDistortioniUnion I c ⊤).tendsto_iff
    (l.hasBasis_toFilterDistortioniUnion J _ _)).2 fun r hr => ?_
  refine ⟨r, hr, fun π hπ => ?_⟩
  rw [mem_setOf_eq, Prepartition.iUnion_top] at hπ
  refine ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_trans (hπ.1.3 hD) (le_max_left _ _), fun _ => ?_⟩, ?_⟩
  · refine ⟨_, π₀.iUnion_compl.trans ?_, le_max_right _ _⟩
    congr 1
    exact (Prepartition.iUnion_single h).trans hπ.2.symm
  · exact hπ.2.trans (Prepartition.iUnion_single _).symm
theorem exists_memBaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π, l.MemBaseSet I c r π ∧ π.toPrepartition ≤ π₀ ∧ π.iUnion = π₀.iUnion := by
  rcases π₀.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r with ⟨π, hle, hH, hr, hd, hU⟩
  refine ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun _ => ⟨π₀.compl, ?_, hc₂⟩⟩, ⟨hle, hU⟩⟩
  exact Prepartition.compl_congr hU ▸ π.toPrepartition.iUnion_compl
theorem exists_memBaseSet_isPartition (l : IntegrationParams) (I : Box ι) (hc : I.distortion ≤ c)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) : ∃ π, l.MemBaseSet I c r π ∧ π.IsPartition := by
  rw [← Prepartition.distortion_top] at hc
  have hc' : (⊤ : Prepartition I).compl.distortion ≤ c := by simp
  simpa [isPartition_iff_iUnion_eq] using l.exists_memBaseSet_le_iUnion_eq ⊤ hc hc' r
theorem toFilterDistortioniUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) :
    (l.toFilterDistortioniUnion I c π₀).NeBot :=
  ((l.hasBasis_toFilterDistortion I _).inf_principal _).neBot_iff.2
    fun {r} _ => (l.exists_memBaseSet_le_iUnion_eq π₀ hc₁ hc₂ r).imp fun _ hπ => ⟨hπ.1, hπ.2.2⟩
instance toFilterDistortioniUnion_neBot' (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I (max π₀.distortion π₀.compl.distortion) π₀).NeBot :=
  l.toFilterDistortioniUnion_neBot I π₀ (le_max_left _ _) (le_max_right _ _)
instance toFilterDistortion_neBot (l : IntegrationParams) (I : Box ι) :
    (l.toFilterDistortion I I.distortion).NeBot := by
  simpa using (l.toFilterDistortioniUnion_neBot' I ⊤).mono inf_le_left
instance toFilter_neBot (l : IntegrationParams) (I : Box ι) : (l.toFilter I).NeBot :=
  (l.toFilterDistortion_neBot I).mono <| le_iSup _ _
instance toFilteriUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).NeBot :=
  (l.toFilterDistortioniUnion_neBot' I π₀).mono <|
    le_iSup (fun c => l.toFilterDistortioniUnion I c π₀) _
theorem eventually_isPartition (l : IntegrationParams) (I : Box ι) :
    ∀ᶠ π in l.toFilteriUnion I ⊤, TaggedPrepartition.IsPartition π :=
  eventually_iSup.2 fun _ =>
    eventually_inf_principal.2 <|
      Eventually.of_forall fun π h =>
        π.isPartition_iff_iUnion_eq.2 (h.trans Prepartition.iUnion_top)
end IntegrationParams
end BoxIntegral