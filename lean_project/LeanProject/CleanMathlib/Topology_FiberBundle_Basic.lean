import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Topology.Order.LeftRightNhds
variable {ι B F X : Type*} [TopologicalSpace X]
open TopologicalSpace Filter Set Bundle Topology
section FiberBundle
variable (F)
variable [TopologicalSpace B] [TopologicalSpace F] (E : B → Type*)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
class FiberBundle where
  totalSpaceMk_isInducing' : ∀ b : B, IsInducing (@TotalSpace.mk B F E b)
  trivializationAtlas' : Set (Trivialization F (π F E))
  trivializationAt' : B → Trivialization F (π F E)
  mem_baseSet_trivializationAt' : ∀ b : B, b ∈ (trivializationAt' b).baseSet
  trivialization_mem_atlas' : ∀ b : B, trivializationAt' b ∈ trivializationAtlas'
namespace FiberBundle
variable [FiberBundle F E] (b : B)
theorem totalSpaceMk_isInducing : IsInducing (@TotalSpace.mk B F E b) := totalSpaceMk_isInducing' b
@[deprecated (since := "2024-10-28")] alias totalSpaceMk_inducing := totalSpaceMk_isInducing
abbrev trivializationAtlas : Set (Trivialization F (π F E)) := trivializationAtlas'
abbrev trivializationAt : Trivialization F (π F E) := trivializationAt' b
theorem mem_baseSet_trivializationAt : b ∈ (trivializationAt F E b).baseSet :=
  mem_baseSet_trivializationAt' b
theorem trivialization_mem_atlas : trivializationAt F E b ∈ trivializationAtlas F E :=
  trivialization_mem_atlas' b
end FiberBundle
export FiberBundle (totalSpaceMk_isInducing trivializationAtlas trivializationAt
  mem_baseSet_trivializationAt trivialization_mem_atlas)
variable {F}
variable {E}
@[mk_iff]
class MemTrivializationAtlas [FiberBundle F E] (e : Trivialization F (π F E)) : Prop where
  out : e ∈ trivializationAtlas F E
instance [FiberBundle F E] (b : B) : MemTrivializationAtlas (trivializationAt F E b) where
  out := trivialization_mem_atlas F E b
namespace FiberBundle
variable (F)
variable [FiberBundle F E]
theorem map_proj_nhds (x : TotalSpace F E) : map (π F E) (𝓝 x) = 𝓝 x.proj :=
  (trivializationAt F E x.proj).map_proj_nhds <|
    (trivializationAt F E x.proj).mem_source.2 <| mem_baseSet_trivializationAt F E x.proj
variable (E)
@[continuity]
theorem continuous_proj : Continuous (π F E) :=
  continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le
theorem isOpenMap_proj : IsOpenMap (π F E) :=
  IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge
theorem surjective_proj [Nonempty F] : Function.Surjective (π F E) := fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩
theorem isQuotientMap_proj [Nonempty F] : IsQuotientMap (π F E) :=
  (isOpenMap_proj F E).isQuotientMap (continuous_proj F E) (surjective_proj F E)
@[deprecated (since := "2024-10-22")]
alias quotientMap_proj := isQuotientMap_proj
theorem continuous_totalSpaceMk (x : B) : Continuous (@TotalSpace.mk B F E x) :=
  (totalSpaceMk_isInducing F E x).continuous
theorem totalSpaceMk_isEmbedding (x : B) : IsEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isInducing F E x, TotalSpace.mk_injective x⟩
@[deprecated (since := "2024-10-26")]
alias totalSpaceMk_embedding := totalSpaceMk_isEmbedding
theorem totalSpaceMk_isClosedEmbedding [T1Space B] (x : B) :
    IsClosedEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isEmbedding F E x, by
    rw [TotalSpace.range_mk]
    exact isClosed_singleton.preimage <| continuous_proj F E⟩
@[deprecated (since := "2024-10-20")]
alias totalSpaceMk_closedEmbedding := totalSpaceMk_isClosedEmbedding
variable {E F}
@[simp, mfld_simps]
theorem mem_trivializationAt_proj_source {x : TotalSpace F E} :
    x ∈ (trivializationAt F E x.proj).source :=
  (Trivialization.mem_source _).mpr <| mem_baseSet_trivializationAt F E x.proj
theorem trivializationAt_proj_fst {x : TotalSpace F E} :
    ((trivializationAt F E x.proj) x).1 = x.proj :=
  Trivialization.coe_fst' _ <| mem_baseSet_trivializationAt F E x.proj
variable (F)
open Trivialization
theorem continuousWithinAt_totalSpace (f : X → TotalSpace F E) {s : Set X} {x₀ : X} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x => (f x).proj) s x₀ ∧
        ContinuousWithinAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) s x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source
theorem continuousAt_totalSpace (f : X → TotalSpace F E) {x₀ : X} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).proj) x₀ ∧
        ContinuousAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) x₀ :=
  (trivializationAt F E (f x₀).proj).tendsto_nhds_iff mem_trivializationAt_proj_source
end FiberBundle
variable (F)
variable (E)
theorem FiberBundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] [FiberBundle F E] (a b : B) :
    ∃ e : Trivialization F (π F E), Icc a b ⊆ e.baseSet := by
  obtain ⟨ea, hea⟩ : ∃ ea : Trivialization F (π F E), a ∈ ea.baseSet :=
    ⟨trivializationAt F E a, mem_baseSet_trivializationAt F E a⟩
  cases' lt_or_le b a with hab hab
  · exact ⟨ea, by simp [*]⟩
  set s : Set B := { x ∈ Icc a b | ∃ e : Trivialization F (π F E), Icc a x ⊆ e.baseSet }
  have ha : a ∈ s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : Trivialization F (π F E), hec : Icc a c ⊆ ec.baseSet⟩ : c ∈ s := by
    rcases hc.1.eq_or_lt with heq | hlt
    · rwa [← heq]
    refine ⟨hc, ?_⟩
    obtain ⟨ec, hc⟩ : ∃ ec : Trivialization F (π F E), c ∈ ec.baseSet :=
      ⟨trivializationAt F E c, mem_baseSet_trivializationAt F E c⟩
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.baseSet :=
      (mem_nhdsWithin_Iic_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet hc)
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2
    refine ⟨ead.piecewiseLe ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 ?_⟩
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
  rcases hc.2.eq_or_lt with heq | hlt
  · exact ⟨ec, heq ▸ hec⟩
  rsuffices ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, ∃ e : Trivialization F (π F E), Icc a d ⊆ e.baseSet
  · exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_lt hdcb.1).elim
  obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.baseSet :=
    (mem_nhdsWithin_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_baseSet (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d ⊆ ec.baseSet := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases he : Disjoint (Iio d) (Ioi c)
  · 
    obtain ⟨ed, hed⟩ : ∃ ed : Trivialization F (π F E), d ∈ ed.baseSet :=
      ⟨trivializationAt F E d, mem_baseSet_trivializationAt F E d⟩
    refine ⟨d, hdcb,
      (ec.restrOpen (Iio d) isOpen_Iio).disjointUnion (ed.restrOpen (Ioi c) isOpen_Ioi)
        (he.mono inter_subset_right inter_subset_right), fun x hx => ?_⟩
    rcases hx.2.eq_or_lt with (rfl | hxd)
    exacts [Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
  · 
    rw [disjoint_left] at he
    push_neg at he
    rcases he with ⟨d', hdd' : d' < d, hd'c⟩
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩
end FiberBundle
structure FiberBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B] (F : Type*)
    [TopologicalSpace F] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F → F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j,
    ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i ∩ baseSet j) ×ˢ univ)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v
namespace FiberBundleCore
variable [TopologicalSpace B] [TopologicalSpace F] (Z : FiberBundleCore ι B F)
@[nolint unusedArguments] 
def Index (_Z : FiberBundleCore ι B F) := ι
@[nolint unusedArguments, reducible]
def Base (_Z : FiberBundleCore ι B F) := B
@[nolint unusedArguments] 
def Fiber (_ : FiberBundleCore ι B F) (_x : B) := F
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := ‹_›
abbrev TotalSpace := Bundle.TotalSpace F Z.Fiber
@[reducible, simp, mfld_simps]
def proj : Z.TotalSpace → B :=
  Bundle.TotalSpace.proj
def trivChange (i j : ι) : PartialHomeomorph (B × F) (B × F) where
  source := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [coordChange_comp, Z.coordChange_self]
    exacts [hx.1, ⟨⟨hx.1, hx.2⟩, hx.1⟩]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    · exact hx.2
    · simp [hx]
  open_source := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  open_target := ((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prod (Z.continuousOn_coordChange i j)
  continuousOn_invFun := by
    simpa [inter_comm] using continuous_fst.continuousOn.prod (Z.continuousOn_coordChange j i)
@[simp, mfld_simps]
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j := by
  erw [mem_prod]
  simp
def localTrivAsPartialEquiv (i : ι) : PartialEquiv Z.TotalSpace (B × F) where
  source := Z.proj ⁻¹' Z.baseSet i
  target := Z.baseSet i ×ˢ univ
  invFun p := ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun p := ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.prod_mk_mem_set_prod_eq] using hp
  map_target' p hp := by
    simpa only [Set.mem_preimage, and_true, Set.mem_univ, Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    replace hx : x ∈ Z.baseSet i := hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self] <;> apply_rules [mem_baseSet_at, mem_inter]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, and_true, mem_univ] at hx
    dsimp only
    rw [Z.coordChange_comp, Z.coordChange_self]
    exacts [hx, ⟨⟨hx, Z.mem_baseSet_at _⟩, hx⟩]
variable (i : ι)
theorem mem_localTrivAsPartialEquiv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTrivAsPartialEquiv i).source ↔ p.1 ∈ Z.baseSet i :=
  Iff.rfl
theorem mem_localTrivAsPartialEquiv_target (p : B × F) :
    p ∈ (Z.localTrivAsPartialEquiv i).target ↔ p.1 ∈ Z.baseSet i := by
  erw [mem_prod]
  simp only [and_true, mem_univ]
theorem localTrivAsPartialEquiv_apply (p : Z.TotalSpace) :
    (Z.localTrivAsPartialEquiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl
theorem localTrivAsPartialEquiv_trans (i j : ι) :
    (Z.localTrivAsPartialEquiv i).symm.trans (Z.localTrivAsPartialEquiv j) ≈
      (Z.trivChange i j).toPartialEquiv := by
  constructor
  · ext x
    simp only [mem_localTrivAsPartialEquiv_target, mfld_simps]
    rfl
  · rintro ⟨x, v⟩ hx
    simp only [trivChange, localTrivAsPartialEquiv, PartialEquiv.symm,
      Prod.mk.inj_iff, prod_mk_mem_set_prod_eq, PartialEquiv.trans_source, mem_inter_iff,
      mem_preimage, proj, mem_univ, eq_self_iff_true, (· ∘ ·),
      PartialEquiv.coe_trans, TotalSpace.proj] at hx ⊢
    simp only [Z.coordChange_comp, hx, mem_inter_iff, and_self_iff, mem_baseSet_at]
instance toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace F Z.Fiber) :=
  TopologicalSpace.generateFrom <| ⋃ (i : ι) (s : Set (B × F)) (_ : IsOpen s),
    {(Z.localTrivAsPartialEquiv i).source ∩ Z.localTrivAsPartialEquiv i ⁻¹' s}
variable (b : B) (a : F)
theorem open_source' (i : ι) : IsOpen (Z.localTrivAsPartialEquiv i).source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨i, Z.baseSet i ×ˢ univ, (Z.isOpen_baseSet i).prod isOpen_univ, ?_⟩
  ext p
  simp only [localTrivAsPartialEquiv_apply, prod_mk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_localTrivAsPartialEquiv_source, and_true, mem_univ, mem_preimage]
def localTriv (i : ι) : Trivialization F Z.proj where
  baseSet := Z.baseSet i
  open_baseSet := Z.isOpen_baseSet i
  source_eq := rfl
  target_eq := rfl
  proj_toFun p _ := by
    simp only [mfld_simps]
    rfl
  open_source := Z.open_source' i
  open_target := (Z.isOpen_baseSet i).prod isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [exists_prop, mem_iUnion, mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuousOn_invFun := by
    refine continuousOn_isOpen_of_generateFrom fun t ht ↦ ?_
    simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s, IsOpen s ∧
      t = (localTrivAsPartialEquiv Z j).source ∩ localTrivAsPartialEquiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [PartialEquiv.right_inv, preimage_inter, PartialEquiv.left_inv]
    let e := Z.localTrivAsPartialEquiv i
    let e' := Z.localTrivAsPartialEquiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source ∩ f ⁻¹' s) := by
      rw [PartialEquiv.EqOnSource.source_inter_preimage_eq (Z.localTrivAsPartialEquiv_trans i j)]
      exact (continuousOn_open_iff (Z.trivChange i j).open_source).1
        (Z.trivChange i j).continuousOn _ s_open
    convert this using 1
    dsimp [f, PartialEquiv.trans_source]
    rw [← preimage_comp, inter_assoc]
  toPartialEquiv := Z.localTrivAsPartialEquiv i
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)
@[simp, mfld_simps]
theorem localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl
theorem localTrivAt_snd (b : B) (p) :
    (Z.localTrivAt b p).2 = Z.coordChange (Z.indexAt p.1) (Z.indexAt b) p.1 p.2 :=
  rfl
theorem continuous_const_section (v : F)
    (h : ∀ i j, ∀ x ∈ Z.baseSet i ∩ Z.baseSet j, Z.coordChange i j x v = v) :
    Continuous (show B → Z.TotalSpace from fun x => ⟨x, v⟩) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have A : Z.baseSet (Z.indexAt x) ∈ 𝓝 x :=
    IsOpen.mem_nhds (Z.isOpen_baseSet (Z.indexAt x)) (Z.mem_baseSet_at x)
  refine ((Z.localTrivAt x).toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left ?_).2 ?_
  · exact A
  · apply continuousAt_id.prod
    simp only [(· ∘ ·), mfld_simps, localTrivAt_snd]
    have : ContinuousOn (fun _ : B => v) (Z.baseSet (Z.indexAt x)) := continuousOn_const
    refine (this.congr fun y hy ↦ ?_).continuousAt A
    exact h _ _ _ ⟨mem_baseSet_at _ _, hy⟩
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_coe : ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv i :=
  rfl
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_source :
    (Z.localTrivAsPartialEquiv i).source = (Z.localTriv i).source :=
  rfl
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_target :
    (Z.localTrivAsPartialEquiv i).target = (Z.localTriv i).target :=
  rfl
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_symm :
    (Z.localTrivAsPartialEquiv i).symm = (Z.localTriv i).toPartialEquiv.symm :=
  rfl
@[simp, mfld_simps]
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl
@[simp, mfld_simps]
theorem localTriv_apply (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl
@[simp, mfld_simps]
theorem localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ := by
  rw [localTrivAt, localTriv_apply, coordChange_self]
  exact Z.mem_baseSet_at p.1
@[simp, mfld_simps]
theorem localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _
@[simp, mfld_simps]
theorem mem_localTriv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTriv i).source ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Iff.rfl
@[simp, mfld_simps]
theorem mem_localTrivAt_source (p : Z.TotalSpace) (b : B) :
    p ∈ (Z.localTrivAt b).source ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Iff.rfl
@[simp, mfld_simps]
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Trivialization.mem_target _
@[simp, mfld_simps]
theorem mem_localTrivAt_target (p : B × F) (b : B) :
    p ∈ (Z.localTrivAt b).target ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Trivialization.mem_target _
@[simp, mfld_simps]
theorem localTriv_symm_apply (p : B × F) :
    (Z.localTriv i).toPartialHomeomorph.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl
@[simp, mfld_simps]
theorem mem_localTrivAt_baseSet (b : B) : b ∈ (Z.localTrivAt b).baseSet := by
  rw [localTrivAt, ← baseSet_at]
  exact Z.mem_baseSet_at b
theorem mk_mem_localTrivAt_source : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  simp only [mfld_simps]
instance fiberBundle : FiberBundle F Z.Fiber where
  totalSpaceMk_isInducing' b := isInducing_iff_nhds.2 fun x ↦ by
    rw [(Z.localTrivAt b).nhds_eq_comap_inf_principal (mk_mem_localTrivAt_source _ _ _), comap_inf,
      comap_principal, comap_comap]
    simp only [Function.comp_def, localTrivAt_apply_mk, Trivialization.coe_coe,
      ← (isEmbedding_prodMk b).nhds_eq_comap]
    convert_to 𝓝 x = 𝓝 x ⊓ 𝓟 univ
    · congr
      exact eq_univ_of_forall (mk_mem_localTrivAt_source Z _)
    · rw [principal_univ, inf_top_eq]
  trivializationAtlas' := Set.range Z.localTriv
  trivializationAt' := Z.localTrivAt
  mem_baseSet_trivializationAt' := Z.mem_baseSet_at
  trivialization_mem_atlas' b := ⟨Z.indexAt b, rfl⟩
@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    Continuous (TotalSpace.mk b : Z.Fiber b → Bundle.TotalSpace F Z.Fiber) :=
  FiberBundle.continuous_totalSpaceMk F Z.Fiber b
nonrec theorem continuous_proj : Continuous Z.proj :=
  FiberBundle.continuous_proj F Z.Fiber
nonrec theorem isOpenMap_proj : IsOpenMap Z.proj :=
  FiberBundle.isOpenMap_proj F Z.Fiber
end FiberBundleCore
variable (F)
variable (E : B → Type*) [TopologicalSpace B] [TopologicalSpace F]
  [∀ x, TopologicalSpace (E x)]
structure FiberPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivializationAt x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivializationAt x ∈ pretrivializationAtlas
  continuous_trivChange : ∀ e, e ∈ pretrivializationAtlas → ∀ e', e' ∈ pretrivializationAtlas →
    ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source)
  totalSpaceMk_isInducing : ∀ b : B, IsInducing (pretrivializationAt b ∘ TotalSpace.mk b)
namespace FiberPrebundle
variable {F E}
variable (a : FiberPrebundle F E) {e : Pretrivialization F (π F E)}
def totalSpaceTopology (a : FiberPrebundle F E) : TopologicalSpace (TotalSpace F E) :=
  ⨆ (e : Pretrivialization F (π F E)) (_ : e ∈ a.pretrivializationAtlas),
    coinduced e.setSymm instTopologicalSpaceSubtype
theorem continuous_symm_of_mem_pretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @ContinuousOn _ _ _ a.totalSpaceTopology e.toPartialEquiv.symm e.target := by
  refine fun z H U h => preimage_nhdsWithin_coinduced' H (le_def.1 (nhds_mono ?_) U h)
  exact le_iSup₂ (α := TopologicalSpace (TotalSpace F E)) e he
theorem isOpen_source (e : Pretrivialization F (π F E)) :
    IsOpen[a.totalSpaceTopology] e.source := by
  refine isOpen_iSup_iff.mpr fun e' => isOpen_iSup_iff.mpr fun _ => ?_
  refine isOpen_coinduced.mpr (isOpen_induced_iff.mpr ⟨e.target, e.open_target, ?_⟩)
  ext ⟨x, hx⟩
  simp only [mem_preimage, Pretrivialization.setSymm, restrict, e.mem_target, e.mem_source,
    e'.proj_symm_apply hx]
theorem isOpen_target_of_mem_pretrivializationAtlas_inter (e e' : Pretrivialization F (π F E))
    (he' : e' ∈ a.pretrivializationAtlas) :
    IsOpen (e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source) := by
  letI := a.totalSpaceTopology
  obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_symm_of_mem_pretrivializationAtlas he')
    e.source (a.isOpen_source e)
  rw [inter_comm, hu2]
  exact hu1.inter e'.open_target
def trivializationOfMemPretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  let _ := a.totalSpaceTopology
  { e with
    open_source := a.isOpen_source e,
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs => ⟨e ⁻¹' s ∩ e.source,
        isOpen_iSup_iff.mpr fun e' => ?_, by rw [inter_assoc, inter_self]; rfl⟩
      refine isOpen_iSup_iff.mpr fun he' => ?_
      rw [isOpen_coinduced, isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuousOn_iff'.mp (a.continuous_trivChange _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u ∩ e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.isOpen_target_of_mem_pretrivializationAtlas_inter e e' he')
    continuousOn_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }
theorem mem_pretrivializationAt_source (b : B) (x : E b) :
    ⟨b, x⟩ ∈ (a.pretrivializationAt b).source := by
  simp only [(a.pretrivializationAt b).source_eq, mem_preimage, TotalSpace.proj]
  exact a.mem_base_pretrivializationAt b
@[simp]
theorem totalSpaceMk_preimage_source (b : B) :
    TotalSpace.mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  eq_univ_of_forall (a.mem_pretrivializationAt_source b)
@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    Continuous[_, a.totalSpaceTopology] (TotalSpace.mk b) := by
  letI := a.totalSpaceTopology
  let e := a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)
  rw [e.toPartialHomeomorph.continuous_iff_continuous_comp_left
      (a.totalSpaceMk_preimage_source b)]
  exact continuous_iff_le_induced.2 (a.totalSpaceMk_isInducing b).eq_induced.le
theorem inducing_totalSpaceMk_of_inducing_comp (b : B)
    (h : IsInducing (a.pretrivializationAt b ∘ TotalSpace.mk b)) :
    @IsInducing _ _ _ a.totalSpaceTopology (TotalSpace.mk b) := by
  letI := a.totalSpaceTopology
  rw [← restrict_comp_codRestrict (a.mem_pretrivializationAt_source b)] at h
  apply IsInducing.of_codRestrict (a.mem_pretrivializationAt_source b)
  refine h.of_comp ?_ (continuousOn_iff_continuous_restrict.mp
    (a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas b)).continuousOn)
  exact (a.continuous_totalSpaceMk b).codRestrict (a.mem_pretrivializationAt_source b)
def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology _ :=
  let _ := a.totalSpaceTopology
  { totalSpaceMk_isInducing' := fun b ↦ a.inducing_totalSpaceMk_of_inducing_comp b
      (a.totalSpaceMk_isInducing b)
    trivializationAtlas' :=
      { e | ∃ (e₀ : _) (he₀ : e₀ ∈ a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ },
    trivializationAt' := fun x ↦
      a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x),
    mem_baseSet_trivializationAt' := a.mem_base_pretrivializationAt
    trivialization_mem_atlas' := fun x ↦ ⟨_, a.pretrivialization_mem_atlas x, rfl⟩ }
theorem continuous_proj : @Continuous _ _ a.totalSpaceTopology _ (π F E) := by
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  exact FiberBundle.continuous_proj F E
instance {e₀} (he₀ : e₀ ∈ a.pretrivializationAtlas) :
    (letI := a.totalSpaceTopology; letI := a.toFiberBundle
      MemTrivializationAtlas (a.trivializationOfMemPretrivializationAtlas he₀)) :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; ⟨e₀, he₀, rfl⟩
theorem continuousOn_of_comp_right {X : Type*} [TopologicalSpace X] {f : TotalSpace F E → X}
    {s : Set B} (hs : IsOpen s) (hf : ∀ b ∈ s,
      ContinuousOn (f ∘ (a.pretrivializationAt b).toPartialEquiv.symm)
        ((s ∩ (a.pretrivializationAt b).baseSet) ×ˢ (Set.univ : Set F))) :
    @ContinuousOn _ _ a.totalSpaceTopology _ f (π F E ⁻¹' s) := by
  letI := a.totalSpaceTopology
  intro z hz
  let e : Trivialization F (π F E) :=
    a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas z.proj)
  refine (e.continuousAt_of_comp_right ?_
    ((hf z.proj hz).continuousAt (IsOpen.mem_nhds ?_ ?_))).continuousWithinAt
  · exact a.mem_base_pretrivializationAt z.proj
  · exact (hs.inter (a.pretrivializationAt z.proj).open_baseSet).prod isOpen_univ
  refine ⟨?_, mem_univ _⟩
  rw [e.coe_fst]
  · exact ⟨hz, a.mem_base_pretrivializationAt z.proj⟩
  · rw [e.mem_source]
    exact a.mem_base_pretrivializationAt z.proj
end FiberPrebundle