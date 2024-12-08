import Mathlib.Topology.Semicontinuous
import Mathlib.MeasureTheory.Function.AEMeasurableSequence
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Topology.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
open Set Filter MeasureTheory MeasurableSpace TopologicalSpace
open scoped Topology NNReal ENNReal MeasureTheory
universe u v w x y
variable {α β γ δ : Type*} {ι : Sort y} {s t u : Set α}
section OrderTopology
variable (α)
variable [TopologicalSpace α] [SecondCountableTopology α] [LinearOrder α] [OrderTopology α]
theorem borel_eq_generateFrom_Iio : borel α = .generateFrom (range Iio) := by
  refine le_antisymm ?_ (generateFrom_le ?_)
  · rw [borel_eq_generateFrom_of_subbasis (@OrderTopology.topology_eq_generate_intervals α _ _ _)]
    letI : MeasurableSpace α := MeasurableSpace.generateFrom (range Iio)
    have H : ∀ a : α, MeasurableSet (Iio a) := fun a => GenerateMeasurable.basic _ ⟨_, rfl⟩
    refine generateFrom_le ?_
    rintro _ ⟨a, rfl | rfl⟩
    · rcases em (∃ b, a ⋖ b) with ⟨b, hb⟩ | hcovBy
      · rw [hb.Ioi_eq, ← compl_Iio]
        exact (H _).compl
      · rcases isOpen_biUnion_countable (Ioi a) Ioi fun _ _ ↦ isOpen_Ioi with ⟨t, hat, htc, htU⟩
        have : Ioi a = ⋃ b ∈ t, Ici b := by
          refine Subset.antisymm ?_ <| iUnion₂_subset fun b hb ↦ Ici_subset_Ioi.2 (hat hb)
          refine Subset.trans ?_ <| iUnion₂_mono fun _ _ ↦ Ioi_subset_Ici_self
          simpa [CovBy, htU, subset_def] using hcovBy
        simp only [this, ← compl_Iio]
        exact .biUnion htc <| fun _ _ ↦ (H _).compl
    · apply H
  · rw [forall_mem_range]
    intro a
    exact GenerateMeasurable.basic _ isOpen_Iio
theorem borel_eq_generateFrom_Ioi : borel α = .generateFrom (range Ioi) :=
  @borel_eq_generateFrom_Iio αᵒᵈ _ (by infer_instance : SecondCountableTopology α) _ _
theorem borel_eq_generateFrom_Iic :
    borel α = MeasurableSpace.generateFrom (range Iic) := by
  rw [borel_eq_generateFrom_Ioi]
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le fun t ht => ?_
    obtain ⟨u, rfl⟩ := ht
    rw [← compl_Iic]
    exact (MeasurableSpace.measurableSet_generateFrom (mem_range.mpr ⟨u, rfl⟩)).compl
  · refine MeasurableSpace.generateFrom_le fun t ht => ?_
    obtain ⟨u, rfl⟩ := ht
    rw [← compl_Ioi]
    exact (MeasurableSpace.measurableSet_generateFrom (mem_range.mpr ⟨u, rfl⟩)).compl
theorem borel_eq_generateFrom_Ici : borel α = MeasurableSpace.generateFrom (range Ici) :=
  @borel_eq_generateFrom_Iic αᵒᵈ _ _ _ _
end OrderTopology
section Orders
variable [TopologicalSpace α] {mα : MeasurableSpace α} [OpensMeasurableSpace α]
variable {mδ : MeasurableSpace δ}
section Preorder
variable [Preorder α] [OrderClosedTopology α] {a b x : α} {μ : Measure α}
@[simp, measurability]
theorem measurableSet_Ici : MeasurableSet (Ici a) :=
  isClosed_Ici.measurableSet
theorem nullMeasurableSet_Ici : NullMeasurableSet (Ici a) μ :=
  measurableSet_Ici.nullMeasurableSet
@[simp, measurability]
theorem measurableSet_Iic : MeasurableSet (Iic a) :=
  isClosed_Iic.measurableSet
theorem nullMeasurableSet_Iic : NullMeasurableSet (Iic a) μ :=
  measurableSet_Iic.nullMeasurableSet
@[simp, measurability]
theorem measurableSet_Icc : MeasurableSet (Icc a b) :=
  isClosed_Icc.measurableSet
theorem nullMeasurableSet_Icc : NullMeasurableSet (Icc a b) μ :=
  measurableSet_Icc.nullMeasurableSet
instance nhdsWithin_Ici_isMeasurablyGenerated : (𝓝[Ici b] a).IsMeasurablyGenerated :=
  measurableSet_Ici.nhdsWithin_isMeasurablyGenerated _
instance nhdsWithin_Iic_isMeasurablyGenerated : (𝓝[Iic b] a).IsMeasurablyGenerated :=
  measurableSet_Iic.nhdsWithin_isMeasurablyGenerated _
instance nhdsWithin_Icc_isMeasurablyGenerated : IsMeasurablyGenerated (𝓝[Icc a b] x) := by
  rw [← Ici_inter_Iic, nhdsWithin_inter]
  infer_instance
instance atTop_isMeasurablyGenerated : (Filter.atTop : Filter α).IsMeasurablyGenerated :=
  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>
    (measurableSet_Ici : MeasurableSet (Ici a)).principal_isMeasurablyGenerated
instance atBot_isMeasurablyGenerated : (Filter.atBot : Filter α).IsMeasurablyGenerated :=
  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>
    (measurableSet_Iic : MeasurableSet (Iic a)).principal_isMeasurablyGenerated
instance [R1Space α] : IsMeasurablyGenerated (cocompact α) where
  exists_measurable_subset := by
    intro _ hs
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
    exact ⟨(closure t)ᶜ, ht.closure.compl_mem_cocompact, isClosed_closure.measurableSet.compl,
      (compl_subset_compl.2 subset_closure).trans hts⟩
end Preorder
section PartialOrder
variable [PartialOrder α] [OrderClosedTopology α] [SecondCountableTopology α] {a b : α}
@[measurability]
theorem measurableSet_le' : MeasurableSet { p : α × α | p.1 ≤ p.2 } :=
  OrderClosedTopology.isClosed_le'.measurableSet
@[measurability]
theorem measurableSet_le {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet { a | f a ≤ g a } :=
  hf.prod_mk hg measurableSet_le'
end PartialOrder
section LinearOrder
variable [LinearOrder α] [OrderClosedTopology α] {a b x : α} {μ : Measure α}
open Interval
@[simp, measurability]
theorem measurableSet_Iio : MeasurableSet (Iio a) :=
  isOpen_Iio.measurableSet
theorem nullMeasurableSet_Iio : NullMeasurableSet (Iio a) μ :=
  measurableSet_Iio.nullMeasurableSet
@[simp, measurability]
theorem measurableSet_Ioi : MeasurableSet (Ioi a) :=
  isOpen_Ioi.measurableSet
theorem nullMeasurableSet_Ioi : NullMeasurableSet (Ioi a) μ :=
  measurableSet_Ioi.nullMeasurableSet
@[simp, measurability]
theorem measurableSet_Ioo : MeasurableSet (Ioo a b) :=
  isOpen_Ioo.measurableSet
theorem nullMeasurableSet_Ioo : NullMeasurableSet (Ioo a b) μ :=
  measurableSet_Ioo.nullMeasurableSet
@[simp, measurability]
theorem measurableSet_Ioc : MeasurableSet (Ioc a b) :=
  measurableSet_Ioi.inter measurableSet_Iic
theorem nullMeasurableSet_Ioc : NullMeasurableSet (Ioc a b) μ :=
  measurableSet_Ioc.nullMeasurableSet
@[simp, measurability]
theorem measurableSet_Ico : MeasurableSet (Ico a b) :=
  measurableSet_Ici.inter measurableSet_Iio
theorem nullMeasurableSet_Ico : NullMeasurableSet (Ico a b) μ :=
  measurableSet_Ico.nullMeasurableSet
instance nhdsWithin_Ioi_isMeasurablyGenerated : (𝓝[Ioi b] a).IsMeasurablyGenerated :=
  measurableSet_Ioi.nhdsWithin_isMeasurablyGenerated _
instance nhdsWithin_Iio_isMeasurablyGenerated : (𝓝[Iio b] a).IsMeasurablyGenerated :=
  measurableSet_Iio.nhdsWithin_isMeasurablyGenerated _
instance nhdsWithin_uIcc_isMeasurablyGenerated : IsMeasurablyGenerated (𝓝[[[a, b]]] x) :=
  nhdsWithin_Icc_isMeasurablyGenerated
@[measurability]
theorem measurableSet_lt' [SecondCountableTopology α] : MeasurableSet { p : α × α | p.1 < p.2 } :=
  (isOpen_lt continuous_fst continuous_snd).measurableSet
@[measurability]
theorem measurableSet_lt [SecondCountableTopology α] {f g : δ → α} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { a | f a < g a } :=
  hf.prod_mk hg measurableSet_lt'
theorem nullMeasurableSet_lt [SecondCountableTopology α] {μ : Measure δ} {f g : δ → α}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : NullMeasurableSet { a | f a < g a } μ :=
  (hf.prod_mk hg).nullMeasurable measurableSet_lt'
theorem nullMeasurableSet_lt' [SecondCountableTopology α] {μ : Measure (α × α)} :
    NullMeasurableSet { p : α × α | p.1 < p.2 } μ :=
  measurableSet_lt'.nullMeasurableSet
theorem nullMeasurableSet_le [SecondCountableTopology α] {μ : Measure δ}
    {f g : δ → α} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { a | f a ≤ g a } μ :=
  (hf.prod_mk hg).nullMeasurable measurableSet_le'
theorem Set.OrdConnected.measurableSet (h : OrdConnected s) : MeasurableSet s := by
  let u := ⋃ (x ∈ s) (y ∈ s), Ioo x y
  have huopen : IsOpen u := isOpen_biUnion fun _ _ => isOpen_biUnion fun _ _ => isOpen_Ioo
  have humeas : MeasurableSet u := huopen.measurableSet
  have hfinite : (s \ u).Finite := s.finite_diff_iUnion_Ioo
  have : u ⊆ s := iUnion₂_subset fun x hx => iUnion₂_subset fun y hy =>
    Ioo_subset_Icc_self.trans (h.out hx hy)
  rw [← union_diff_cancel this]
  exact humeas.union hfinite.measurableSet
theorem IsPreconnected.measurableSet (h : IsPreconnected s) : MeasurableSet s :=
  h.ordConnected.measurableSet
theorem generateFrom_Ico_mem_le_borel {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] (s t : Set α) :
    MeasurableSpace.generateFrom { S | ∃ l ∈ s, ∃ u ∈ t, l < u ∧ Ico l u = S }
      ≤ borel α := by
  apply generateFrom_le
  borelize α
  rintro _ ⟨a, -, b, -, -, rfl⟩
  exact measurableSet_Ico
theorem Dense.borel_eq_generateFrom_Ico_mem_aux {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] {s : Set α} (hd : Dense s)
    (hbot : ∀ x, IsBot x → x ∈ s) (hIoo : ∀ x y : α, x < y → Ioo x y = ∅ → y ∈ s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S } := by
  set S : Set (Set α) := { S | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S }
  refine le_antisymm ?_ (generateFrom_Ico_mem_le_borel _ _)
  letI : MeasurableSpace α := generateFrom S
  rw [borel_eq_generateFrom_Iio]
  refine generateFrom_le (forall_mem_range.2 fun a => ?_)
  rcases hd.exists_countable_dense_subset_bot_top with ⟨t, hts, hc, htd, htb, -⟩
  by_cases ha : ∀ b < a, (Ioo b a).Nonempty
  · convert_to MeasurableSet (⋃ (l ∈ t) (u ∈ t) (_ : l < u) (_ : u ≤ a), Ico l u)
    · ext y
      simp only [mem_iUnion, mem_Iio, mem_Ico]
      constructor
      · intro hy
        rcases htd.exists_le' (fun b hb => htb _ hb (hbot b hb)) y with ⟨l, hlt, hly⟩
        rcases htd.exists_mem_open isOpen_Ioo (ha y hy) with ⟨u, hut, hyu, hua⟩
        exact ⟨l, hlt, u, hut, hly.trans_lt hyu, hua.le, hly, hyu⟩
      · rintro ⟨l, -, u, -, -, hua, -, hyu⟩
        exact hyu.trans_le hua
    · refine MeasurableSet.biUnion hc fun a ha => MeasurableSet.biUnion hc fun b hb => ?_
      refine MeasurableSet.iUnion fun hab => MeasurableSet.iUnion fun _ => ?_
      exact .basic _ ⟨a, hts ha, b, hts hb, hab, mem_singleton _⟩
  · simp only [not_forall, not_nonempty_iff_eq_empty] at ha
    replace ha : a ∈ s := hIoo ha.choose a ha.choose_spec.fst ha.choose_spec.snd
    convert_to MeasurableSet (⋃ (l ∈ t) (_ : l < a), Ico l a)
    · symm
      simp only [← Ici_inter_Iio, ← iUnion_inter, inter_eq_right, subset_def, mem_iUnion,
        mem_Ici, mem_Iio]
      intro x hx
      rcases htd.exists_le' (fun b hb => htb _ hb (hbot b hb)) x with ⟨z, hzt, hzx⟩
      exact ⟨z, hzt, hzx.trans_lt hx, hzx⟩
    · refine .biUnion hc fun x hx => MeasurableSet.iUnion fun hlt => ?_
      exact .basic _ ⟨x, hts hx, a, ha, hlt, mem_singleton _⟩
theorem Dense.borel_eq_generateFrom_Ico_mem {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] [DenselyOrdered α] [NoMinOrder α] {s : Set α}
    (hd : Dense s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S } :=
  hd.borel_eq_generateFrom_Ico_mem_aux (by simp) fun _ _ hxy H =>
    ((nonempty_Ioo.2 hxy).ne_empty H).elim
theorem borel_eq_generateFrom_Ico (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ (l u : α), l < u ∧ Ico l u = S } := by
  simpa only [exists_prop, mem_univ, true_and] using
    (@dense_univ α _).borel_eq_generateFrom_Ico_mem_aux (fun _ _ => mem_univ _) fun _ _ _ _ =>
      mem_univ _
theorem Dense.borel_eq_generateFrom_Ioc_mem_aux {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] {s : Set α} (hd : Dense s)
    (hbot : ∀ x, IsTop x → x ∈ s) (hIoo : ∀ x y : α, x < y → Ioo x y = ∅ → x ∈ s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ioc l u = S } := by
  convert hd.orderDual.borel_eq_generateFrom_Ico_mem_aux hbot fun x y hlt he => hIoo y x hlt _
    using 2
  · ext s
    constructor <;> rintro ⟨l, hl, u, hu, hlt, rfl⟩
    exacts [⟨u, hu, l, hl, hlt, dual_Ico⟩, ⟨u, hu, l, hl, hlt, dual_Ioc⟩]
  · erw [dual_Ioo]
    exact he
theorem Dense.borel_eq_generateFrom_Ioc_mem {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] [DenselyOrdered α] [NoMaxOrder α] {s : Set α}
    (hd : Dense s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ioc l u = S } :=
  hd.borel_eq_generateFrom_Ioc_mem_aux (by simp) fun _ _ hxy H =>
    ((nonempty_Ioo.2 hxy).ne_empty H).elim
theorem borel_eq_generateFrom_Ioc (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ l u, l < u ∧ Ioc l u = S } := by
  simpa only [exists_prop, mem_univ, true_and] using
    (@dense_univ α _).borel_eq_generateFrom_Ioc_mem_aux (fun _ _ => mem_univ _) fun _ _ _ _ =>
      mem_univ _
namespace MeasureTheory.Measure
theorem ext_of_Ico_finite {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) :
    μ = ν := by
  refine
    ext_of_generate_finite _ (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico α))
      (isPiSystem_Ico (id : α → α) id) ?_ hμν
  rintro - ⟨a, b, hlt, rfl⟩
  exact h hlt
theorem ext_of_Ioc_finite {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) :
    μ = ν := by
  refine @ext_of_Ico_finite αᵒᵈ _ _ _ _ _ ‹_› μ ν _ hμν fun a b hab => ?_
  erw [dual_Ico (α := α)]
  exact h hab
theorem ext_of_Ico' {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] [NoMaxOrder α]
    (μ ν : Measure α) (hμ : ∀ ⦃a b⦄, a < b → μ (Ico a b) ≠ ∞)
    (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν := by
  rcases exists_countable_dense_bot_top α with ⟨s, hsc, hsd, hsb, _⟩
  have : (⋃ (l ∈ s) (u ∈ s) (_ : l < u), {Ico l u} : Set (Set α)).Countable :=
    hsc.biUnion fun l _ => hsc.biUnion fun u _ => countable_iUnion fun _ => countable_singleton _
  simp only [← setOf_eq_eq_singleton, ← setOf_exists] at this
  refine
    Measure.ext_of_generateFrom_of_cover_subset
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico α)) (isPiSystem_Ico id id) ?_ this
      ?_ ?_ ?_
  · rintro _ ⟨l, -, u, -, h, rfl⟩
    exact ⟨l, u, h, rfl⟩
  · refine sUnion_eq_univ_iff.2 fun x => ?_
    rcases hsd.exists_le' hsb x with ⟨l, hls, hlx⟩
    rcases hsd.exists_gt x with ⟨u, hus, hxu⟩
    exact ⟨_, ⟨l, hls, u, hus, hlx.trans_lt hxu, rfl⟩, hlx, hxu⟩
  · rintro _ ⟨l, -, u, -, hlt, rfl⟩
    exact hμ hlt
  · rintro _ ⟨l, u, hlt, rfl⟩
    exact h hlt
theorem ext_of_Ioc' {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] [NoMinOrder α]
    (μ ν : Measure α) (hμ : ∀ ⦃a b⦄, a < b → μ (Ioc a b) ≠ ∞)
    (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) : μ = ν := by
  refine @ext_of_Ico' αᵒᵈ _ _ _ _ _ ‹_› _ μ ν ?_ ?_ <;> intro a b hab <;> erw [dual_Ico (α := α)]
  exacts [hμ hab, h hab]
theorem ext_of_Ico {α : Type*} [TopologicalSpace α] {_m : MeasurableSpace α}
    [SecondCountableTopology α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [BorelSpace α] [NoMaxOrder α] (μ ν : Measure α) [IsLocallyFiniteMeasure μ]
    (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν :=
  μ.ext_of_Ico' ν (fun _ _ _ => measure_Ico_lt_top.ne) h
theorem ext_of_Ioc {α : Type*} [TopologicalSpace α] {_m : MeasurableSpace α}
    [SecondCountableTopology α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [BorelSpace α] [NoMinOrder α] (μ ν : Measure α) [IsLocallyFiniteMeasure μ]
    (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) : μ = ν :=
  μ.ext_of_Ioc' ν (fun _ _ _ => measure_Ioc_lt_top.ne) h
theorem ext_of_Iic {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (h : ∀ a, μ (Iic a) = ν (Iic a)) : μ = ν := by
  refine ext_of_Ioc_finite μ ν ?_ fun a b hlt => ?_
  · rcases exists_countable_dense_bot_top α with ⟨s, hsc, hsd, -, hst⟩
    have : DirectedOn (· ≤ ·) s := directedOn_iff_directed.2 (Subtype.mono_coe _).directed_le
    simp only [← biSup_measure_Iic hsc (hsd.exists_ge' hst) this, h]
  rw [← Iic_diff_Iic, measure_diff (Iic_subset_Iic.2 hlt.le) nullMeasurableSet_Iic,
    measure_diff (Iic_subset_Iic.2 hlt.le) nullMeasurableSet_Iic, h a, h b]
  · rw [← h a]
    exact measure_ne_top μ _
  · exact measure_ne_top μ _
theorem ext_of_Ici {α : Type*} [TopologicalSpace α] {_ : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (h : ∀ a, μ (Ici a) = ν (Ici a)) : μ = ν :=
  @ext_of_Iic αᵒᵈ _ _ _ _ _ ‹_› _ _ _ h
end MeasureTheory.Measure
@[measurability]
theorem measurableSet_uIcc : MeasurableSet (uIcc a b) :=
  measurableSet_Icc
@[measurability]
theorem measurableSet_uIoc : MeasurableSet (uIoc a b) :=
  measurableSet_Ioc
variable [SecondCountableTopology α]
@[measurability]
theorem Measurable.max {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => max (f a) (g a) := by
  simpa only [max_def'] using hf.piecewise (measurableSet_le hg hf) hg
@[measurability]
nonrec theorem AEMeasurable.max {f g : δ → α} {μ : Measure δ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => max (f a) (g a)) μ :=
  ⟨fun a => max (hf.mk f a) (hg.mk g a), hf.measurable_mk.max hg.measurable_mk,
    EventuallyEq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩
@[measurability]
theorem Measurable.min {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => min (f a) (g a) := by
  simpa only [min_def] using hf.piecewise (measurableSet_le hf hg) hg
@[measurability]
nonrec theorem AEMeasurable.min {f g : δ → α} {μ : Measure δ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => min (f a) (g a)) μ :=
  ⟨fun a => min (hf.mk f a) (hg.mk g a), hf.measurable_mk.min hg.measurable_mk,
    EventuallyEq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩
end LinearOrder
section Lattice
variable [TopologicalSpace γ] {mγ : MeasurableSpace γ} [BorelSpace γ]
instance (priority := 100) ContinuousSup.measurableSup [Max γ] [ContinuousSup γ] :
    MeasurableSup γ where
  measurable_const_sup _ := (continuous_const.sup continuous_id).measurable
  measurable_sup_const _ := (continuous_id.sup continuous_const).measurable
instance (priority := 100) ContinuousSup.measurableSup₂ [SecondCountableTopology γ] [Max γ]
    [ContinuousSup γ] : MeasurableSup₂ γ :=
  ⟨continuous_sup.measurable⟩
instance (priority := 100) ContinuousInf.measurableInf [Min γ] [ContinuousInf γ] :
    MeasurableInf γ where
  measurable_const_inf _ := (continuous_const.inf continuous_id).measurable
  measurable_inf_const _ := (continuous_id.inf continuous_const).measurable
instance (priority := 100) ContinuousInf.measurableInf₂ [SecondCountableTopology γ] [Min γ]
    [ContinuousInf γ] : MeasurableInf₂ γ :=
  ⟨continuous_inf.measurable⟩
end Lattice
end Orders
section BorelSpace
variable [TopologicalSpace α] {mα : MeasurableSpace α} [BorelSpace α]
variable [TopologicalSpace β] {mβ : MeasurableSpace β} [BorelSpace β]
variable {mδ : MeasurableSpace δ}
section LinearOrder
variable [LinearOrder α] [OrderTopology α] [SecondCountableTopology α]
theorem measurable_of_Iio {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Iio x)) : Measurable f := by
  convert measurable_generateFrom (α := δ) _
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio _)
  · rintro _ ⟨x, rfl⟩; exact hf x
theorem UpperSemicontinuous.measurable [TopologicalSpace δ] [OpensMeasurableSpace δ] {f : δ → α}
    (hf : UpperSemicontinuous f) : Measurable f :=
  measurable_of_Iio fun y => (hf.isOpen_preimage y).measurableSet
theorem measurable_of_Ioi {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Ioi x)) : Measurable f := by
  convert measurable_generateFrom (α := δ) _
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi _)
  · rintro _ ⟨x, rfl⟩; exact hf x
theorem LowerSemicontinuous.measurable [TopologicalSpace δ] [OpensMeasurableSpace δ] {f : δ → α}
    (hf : LowerSemicontinuous f) : Measurable f :=
  measurable_of_Ioi fun y => (hf.isOpen_preimage y).measurableSet
theorem measurable_of_Iic {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Iic x)) : Measurable f := by
  apply measurable_of_Ioi
  simp_rw [← compl_Iic, preimage_compl, MeasurableSet.compl_iff]
  assumption
theorem measurable_of_Ici {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Ici x)) : Measurable f := by
  apply measurable_of_Iio
  simp_rw [← compl_Ici, preimage_compl, MeasurableSet.compl_iff]
  assumption
theorem Measurable.isLUB {ι} [Countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, Measurable (f i))
    (hg : ∀ b, IsLUB { a | ∃ i, f i b = a } (g b)) : Measurable g := by
  change ∀ b, IsLUB (range fun i => f i b) (g b) at hg
  rw [‹BorelSpace α›.measurable_eq, borel_eq_generateFrom_Ioi α]
  apply measurable_generateFrom
  rintro _ ⟨a, rfl⟩
  simp_rw [Set.preimage, mem_Ioi, lt_isLUB_iff (hg _), exists_range_iff, setOf_exists]
  exact MeasurableSet.iUnion fun i => hf i (isOpen_lt' _).measurableSet
theorem Measurable.isLUB_of_mem {ι} [Countable ι] {f : ι → δ → α} {g g' : δ → α}
    (hf : ∀ i, Measurable (f i))
    {s : Set δ} (hs : MeasurableSet s) (hg : ∀ b ∈ s, IsLUB { a | ∃ i, f i b = a } (g b))
    (hg' : EqOn g g' sᶜ) (g'_meas : Measurable g') : Measurable g := by
  classical
  rcases isEmpty_or_nonempty ι with hι|⟨⟨i⟩⟩
  · rcases eq_empty_or_nonempty s with rfl|⟨x, hx⟩
    · convert g'_meas
      rwa [compl_empty, eqOn_univ] at hg'
    · have A : ∀ b ∈ s, IsBot (g b) := by simpa using hg
      have B : ∀ b ∈ s, g b = g x := by
        intro b hb
        apply le_antisymm (A b hb (g x)) (A x hx (g b))
      have : g = s.piecewise (fun _y ↦ g x) g' := by
        ext b
        by_cases hb : b ∈ s
        · simp [hb, B]
        · simp [hb, hg' hb]
      rw [this]
      exact Measurable.piecewise hs measurable_const g'_meas
  · have : Nonempty ι := ⟨i⟩
    let f' : ι → δ → α := fun i ↦ s.piecewise (f i) g'
    suffices ∀ b, IsLUB { a | ∃ i, f' i b = a } (g b) from
      Measurable.isLUB (fun i ↦ Measurable.piecewise hs (hf i) g'_meas) this
    intro b
    by_cases hb : b ∈ s
    · have A : ∀ i, f' i b = f i b := fun i ↦ by simp [f', hb]
      simpa [A] using hg b hb
    · have A : ∀ i, f' i b = g' b := fun i ↦ by simp [f', hb]
      simp [A, hg' hb, isLUB_singleton]
theorem AEMeasurable.isLUB {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α} {g : δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ᵐ b ∂μ, IsLUB { a | ∃ i, f i b = a } (g b)) :
    AEMeasurable g μ := by
  classical
  nontriviality α
  haveI hα : Nonempty α := inferInstance
  cases' isEmpty_or_nonempty ι with hι hι
  · simp only [IsEmpty.exists_iff, setOf_false, isLUB_empty_iff] at hg
    exact aemeasurable_const' (hg.mono fun a ha => hg.mono fun b hb => (ha _).antisymm (hb _))
  let p : δ → (ι → α) → Prop := fun x f' => IsLUB { a | ∃ i, f' i = a } (g x)
  let g_seq := (aeSeqSet hf p).piecewise g fun _ => hα.some
  have hg_seq : ∀ b, IsLUB { a | ∃ i, aeSeq hf p i b = a } (g_seq b) := by
    intro b
    simp only [g_seq, aeSeq, Set.piecewise]
    split_ifs with h
    · have h_set_eq : { a : α | ∃ i : ι, (hf i).mk (f i) b = a } =
        { a : α | ∃ i : ι, f i b = a } := by
        ext x
        simp_rw [Set.mem_setOf_eq, aeSeq.mk_eq_fun_of_mem_aeSeqSet hf h]
      rw [h_set_eq]
      exact aeSeq.fun_prop_of_mem_aeSeqSet hf h
    · exact IsGreatest.isLUB ⟨(@exists_const (hα.some = hα.some) ι _).2 rfl, fun x ⟨i, hi⟩ => hi.ge⟩
  refine ⟨g_seq, Measurable.isLUB (aeSeq.measurable hf p) hg_seq, ?_⟩
  exact
    (ite_ae_eq_of_measure_compl_zero g (fun _ => hα.some) (aeSeqSet hf p)
        (aeSeq.measure_compl_aeSeqSet_eq_zero hf hg)).symm
theorem Measurable.isGLB {ι} [Countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, Measurable (f i))
    (hg : ∀ b, IsGLB { a | ∃ i, f i b = a } (g b)) : Measurable g :=
  Measurable.isLUB (α := αᵒᵈ) hf hg
theorem Measurable.isGLB_of_mem {ι} [Countable ι] {f : ι → δ → α} {g g' : δ → α}
    (hf : ∀ i, Measurable (f i))
    {s : Set δ} (hs : MeasurableSet s) (hg : ∀ b ∈ s, IsGLB { a | ∃ i, f i b = a } (g b))
    (hg' : EqOn g g' sᶜ) (g'_meas : Measurable g') : Measurable g :=
  Measurable.isLUB_of_mem (α := αᵒᵈ) hf hs hg hg'  g'_meas
theorem AEMeasurable.isGLB {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α} {g : δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ᵐ b ∂μ, IsGLB { a | ∃ i, f i b = a } (g b)) :
    AEMeasurable g μ :=
  AEMeasurable.isLUB (α := αᵒᵈ) hf hg
protected theorem Monotone.measurable [LinearOrder β] [OrderClosedTopology β] {f : β → α}
    (hf : Monotone f) : Measurable f :=
  suffices h : ∀ x, OrdConnected (f ⁻¹' Ioi x) from measurable_of_Ioi fun x => (h x).measurableSet
  fun _ => ordConnected_def.mpr fun _a ha _ _ _c hc => lt_of_lt_of_le ha (hf hc.1)
theorem aemeasurable_restrict_of_monotoneOn [LinearOrder β] [OrderClosedTopology β] {μ : Measure β}
    {s : Set β} (hs : MeasurableSet s) {f : β → α} (hf : MonotoneOn f s) :
    AEMeasurable f (μ.restrict s) :=
  have : Monotone (f ∘ (↑) : s → α) := fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (hxy : x ≤ y) => hf hx hy hxy
  aemeasurable_restrict_of_measurable_subtype hs this.measurable
protected theorem Antitone.measurable [LinearOrder β] [OrderClosedTopology β] {f : β → α}
    (hf : Antitone f) : Measurable f :=
  @Monotone.measurable αᵒᵈ β _ _ ‹_› _ _ _ _ _ ‹_› _ _ _ hf
theorem aemeasurable_restrict_of_antitoneOn [LinearOrder β] [OrderClosedTopology β] {μ : Measure β}
    {s : Set β} (hs : MeasurableSet s) {f : β → α} (hf : AntitoneOn f s) :
    AEMeasurable f (μ.restrict s) :=
  @aemeasurable_restrict_of_monotoneOn αᵒᵈ β _ _ ‹_› _ _ _ _ _ ‹_› _ _ _ _ hs _ hf
theorem measurableSet_of_mem_nhdsWithin_Ioi_aux {s : Set α} (h : ∀ x ∈ s, s ∈ 𝓝[>] x)
    (h' : ∀ x ∈ s, ∃ y, x < y) : MeasurableSet s := by
  choose! M hM using h'
  suffices H : (s \ interior s).Countable by
    have : s = interior s ∪ s \ interior s := by rw [union_diff_cancel interior_subset]
    rw [this]
    exact isOpen_interior.measurableSet.union H.measurableSet
  have A : ∀ x ∈ s, ∃ y ∈ Ioi x, Ioo x y ⊆ s := fun x hx =>
    (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (hM x hx)).1 (h x hx)
  choose! y hy h'y using A
  have B : Set.PairwiseDisjoint (s \ interior s) fun x => Ioo x (y x) := by
    intro x hx x' hx' hxx'
    rcases lt_or_gt_of_ne hxx' with (h' | h')
    · refine disjoint_left.2 fun z hz h'z => ?_
      have : x' ∈ interior s :=
        mem_interior.2 ⟨Ioo x (y x), h'y _ hx.1, isOpen_Ioo, ⟨h', h'z.1.trans hz.2⟩⟩
      exact False.elim (hx'.2 this)
    · refine disjoint_left.2 fun z hz h'z => ?_
      have : x ∈ interior s :=
        mem_interior.2 ⟨Ioo x' (y x'), h'y _ hx'.1, isOpen_Ioo, ⟨h', hz.1.trans h'z.2⟩⟩
      exact False.elim (hx.2 this)
  exact B.countable_of_Ioo fun x hx => hy x hx.1
theorem measurableSet_of_mem_nhdsWithin_Ioi {s : Set α} (h : ∀ x ∈ s, s ∈ 𝓝[>] x) :
    MeasurableSet s := by
  by_cases H : ∃ x ∈ s, IsTop x
  · rcases H with ⟨x₀, x₀s, h₀⟩
    have : s = {x₀} ∪ s \ {x₀} := by rw [union_diff_cancel (singleton_subset_iff.2 x₀s)]
    rw [this]
    refine (measurableSet_singleton _).union ?_
    have A : ∀ x ∈ s \ {x₀}, x < x₀ := fun x hx => lt_of_le_of_ne (h₀ _) (by simpa using hx.2)
    refine measurableSet_of_mem_nhdsWithin_Ioi_aux (fun x hx => ?_) fun x hx => ⟨x₀, A x hx⟩
    obtain ⟨u, hu, us⟩ : ∃ (u : α), u ∈ Ioi x ∧ Ioo x u ⊆ s :=
      (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (A x hx)).1 (h x hx.1)
    refine (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (A x hx)).2 ⟨u, hu, fun y hy => ⟨us hy, ?_⟩⟩
    exact ne_of_lt (hy.2.trans_le (h₀ _))
  · apply measurableSet_of_mem_nhdsWithin_Ioi_aux h
    simp only [IsTop] at H
    push_neg at H
    exact H
lemma measurableSet_bddAbove_range {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet {b | BddAbove (range (fun i ↦ f i b))} := by
  rcases isEmpty_or_nonempty α with hα|hα
  · have : ∀ b, range (fun i ↦ f i b) = ∅ := fun b ↦ eq_empty_of_isEmpty _
    simp [this]
  have A : ∀ (i : ι) (c : α), MeasurableSet {x | f i x ≤ c} := by
    intro i c
    exact measurableSet_le (hf i) measurable_const
  have B : ∀ (c : α), MeasurableSet {x | ∀ i, f i x ≤ c} := by
    intro c
    rw [setOf_forall]
    exact MeasurableSet.iInter (fun i ↦ A i c)
  obtain ⟨u, hu⟩ : ∃ (u : ℕ → α), Tendsto u atTop atTop := exists_seq_tendsto (atTop : Filter α)
  have : {b | BddAbove (range (fun i ↦ f i b))} = {x | ∃ n, ∀ i, f i x ≤ u n} := by
    apply Subset.antisymm
    · rintro x ⟨c, hc⟩
      obtain ⟨n, hn⟩ : ∃ n, c ≤ u n := (tendsto_atTop.1 hu c).exists
      exact ⟨n, fun i ↦ (hc ((mem_range_self i))).trans hn⟩
    · rintro x ⟨n, hn⟩
      refine ⟨u n, ?_⟩
      rintro - ⟨i, rfl⟩
      exact hn i
  rw [this, setOf_exists]
  exact MeasurableSet.iUnion (fun n ↦ B (u n))
lemma measurableSet_bddBelow_range {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet {b | BddBelow (range (fun i ↦ f i b))} :=
  measurableSet_bddAbove_range (α := αᵒᵈ) hf
end LinearOrder
section ConditionallyCompleteLattice
@[measurability]
theorem Measurable.iSup_Prop {α} {mα : MeasurableSpace α} [ConditionallyCompleteLattice α]
    (p : Prop) {f : δ → α} (hf : Measurable f) : Measurable fun b => ⨆ _ : p, f b := by
  classical
  simp_rw [ciSup_eq_ite]
  split_ifs with h
  · exact hf
  · exact measurable_const
@[measurability]
theorem Measurable.iInf_Prop {α} {mα : MeasurableSpace α} [ConditionallyCompleteLattice α]
    (p : Prop) {f : δ → α} (hf : Measurable f) : Measurable fun b => ⨅ _ : p, f b := by
  classical
  simp_rw [ciInf_eq_ite]
  split_ifs with h
  · exact hf
  · exact measurable_const
end ConditionallyCompleteLattice
section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] [OrderTopology α] [SecondCountableTopology α]
@[measurability, fun_prop]
protected theorem Measurable.iSup {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun b ↦ ⨆ i, f i b) := by
  rcases isEmpty_or_nonempty ι with hι|hι
  · simp [iSup_of_empty']
  have A : MeasurableSet {b | BddAbove (range (fun i ↦ f i b))} :=
    measurableSet_bddAbove_range hf
  have : Measurable (fun (_b : δ) ↦ sSup (∅ : Set α)) := measurable_const
  apply Measurable.isLUB_of_mem hf A _ _ this
  · rintro b ⟨c, hc⟩
    apply isLUB_ciSup
    refine ⟨c, ?_⟩
    rintro d ⟨i, rfl⟩
    exact hc (mem_range_self i)
  · intro b hb
    apply csSup_of_not_bddAbove
    exact hb
@[deprecated (since := "2024-10-21")]
alias measurable_iSup := Measurable.iSup
@[measurability]
protected theorem AEMeasurable.iSup {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨆ i, f i b) μ := by
  refine ⟨fun b ↦ ⨆ i, (hf i).mk (f i) b, .iSup (fun i ↦ (hf i).measurable_mk), ?_⟩
  filter_upwards [ae_all_iff.2 (fun i ↦ (hf i).ae_eq_mk)] with b hb using by simp [hb]
@[deprecated (since := "2024-10-21")]
alias aemeasurable_iSup := AEMeasurable.iSup
@[measurability, fun_prop]
protected theorem Measurable.iInf {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun b => ⨅ i, f i b :=
  .iSup (α := αᵒᵈ) hf
@[deprecated (since := "2024-10-21")]
alias measurable_iInf := Measurable.iInf
@[measurability]
protected theorem AEMeasurable.iInf {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨅ i, f i b) μ :=
  .iSup (α := αᵒᵈ) hf
@[deprecated (since := "2024-10-21")]
alias aemeasurable_iInf := AEMeasurable.iInf
protected theorem Measurable.sSup {ι} {f : ι → δ → α} {s : Set ι} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x => sSup ((fun i => f i x) '' s) := by
  simp_rw [image_eq_range]
  have : Countable s := hs.to_subtype
  exact .iSup fun i ↦ hf i i.2
@[deprecated (since := "2024-10-21")]
alias measurable_sSup := Measurable.sSup
protected theorem Measurable.sInf {ι} {f : ι → δ → α} {s : Set ι} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x => sInf ((fun i => f i x) '' s) :=
  .sSup (α := αᵒᵈ) hs hf
@[deprecated (since := "2024-10-21")]
alias measurable_sInf := Measurable.sInf
theorem Measurable.biSup {ι} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun b => ⨆ i ∈ s, f i b := by
  haveI : Encodable s := hs.toEncodable
  by_cases H : ∀ i, i ∈ s
  · have : ∀ b, ⨆ i ∈ s, f i b = ⨆ (i : s), f i b :=
      fun b ↦ cbiSup_eq_of_forall (f := fun i ↦ f i b) H
    simp only [this]
    exact .iSup (fun (i : s) ↦ hf i i.2)
  · have : ∀ b, ⨆ i ∈ s, f i b = (⨆ (i : s), f i b) ⊔ sSup ∅ :=
      fun b ↦ cbiSup_eq_of_not_forall (f := fun i ↦ f i b) H
    simp only [this]
    apply Measurable.sup _ measurable_const
    exact .iSup (fun (i : s) ↦ hf i i.2)
@[deprecated (since := "2024-10-21")]
alias measurable_biSup := Measurable.biSup
theorem AEMeasurable.biSup {ι} {μ : Measure δ} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨆ i ∈ s, f i b) μ := by
  classical
  let g : ι → δ → α := fun i ↦ if hi : i ∈ s then (hf i hi).mk (f i) else fun _b ↦ sSup ∅
  have : ∀ i ∈ s, Measurable (g i) := by
    intro i hi
    simpa [g, hi] using (hf i hi).measurable_mk
  refine ⟨fun b ↦ ⨆ (i) (_ : i ∈ s), g i b, .biSup s hs this, ?_⟩
  have : ∀ i ∈ s, ∀ᵐ b ∂μ, f i b = g i b :=
    fun i hi ↦ by simpa [g, hi] using (hf i hi).ae_eq_mk
  filter_upwards [(ae_ball_iff hs).2 this] with b hb
  exact iSup_congr fun i => iSup_congr (hb i)
@[deprecated (since := "2024-10-21")]
alias aemeasurable_biSup := AEMeasurable.biSup
theorem Measurable.biInf {ι} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun b => ⨅ i ∈ s, f i b :=
  .biSup (α := αᵒᵈ) s hs hf
@[deprecated (since := "2024-10-21")]
alias measurable_biInf := Measurable.biInf
theorem AEMeasurable.biInf {ι} {μ : Measure δ} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨅ i ∈ s, f i b) μ :=
  .biSup (α := αᵒᵈ) s hs hf
@[deprecated (since := "2024-10-21")]
alias aemeasurable_biInf := AEMeasurable.biInf
theorem Measurable.liminf' {ι ι'} {f : ι → δ → α} {v : Filter ι} (hf : ∀ i, Measurable (f i))
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasCountableBasis p s) (hs : ∀ j, (s j).Countable) :
    Measurable fun x => liminf (f · x) v := by
  classical
  have : Countable (Subtype p) := hv.countable
  rcases isEmpty_or_nonempty (Subtype p) with hp|hp
  · simp [hv.liminf_eq_sSup_iUnion_iInter]
  by_cases H : ∃ (j : Subtype p), s j = ∅
  · simp_rw [hv.liminf_eq_ite, if_pos H, measurable_const]
  simp_rw [hv.liminf_eq_ite, if_neg H]
  have : ∀ i, Countable (s i) := fun i ↦ countable_coe_iff.2 (hs i)
  let m : Subtype p → Set δ := fun j ↦ {x | BddBelow (range (fun (i : s j) ↦ f i x))}
  have m_meas : ∀ j, MeasurableSet (m j) :=
    fun j ↦ measurableSet_bddBelow_range (fun (i : s j) ↦ hf i)
  have mc_meas : MeasurableSet {x | ∀ (j : Subtype p), x ∉ m j} := by
    rw [setOf_forall]
    exact MeasurableSet.iInter (fun j ↦ (m_meas j).compl)
  refine measurable_const.piecewise mc_meas <| .iSup fun j ↦ ?_
  let reparam : δ → Subtype p → Subtype p := fun x ↦ liminf_reparam (fun i ↦ f i x) s p
  let F0 : Subtype p → δ → α := fun j x ↦ ⨅ (i : s j), f i x
  have F0_meas : ∀ j, Measurable (F0 j) := fun j ↦ .iInf (fun (i : s j) ↦ hf i)
  set F1 : δ → α := fun x ↦ F0 (reparam x j) x with hF1
  change Measurable F1
  let g : ℕ → Subtype p := Classical.choose (exists_surjective_nat (Subtype p))
  have Z : ∀ x, ∃ n, x ∈ m (g n) ∨ ∀ k, x ∉ m k := by
    intro x
    by_cases H : ∃ k, x ∈ m k
    · rcases H with ⟨k, hk⟩
      rcases Classical.choose_spec (exists_surjective_nat (Subtype p)) k with ⟨n, rfl⟩
      exact ⟨n, Or.inl hk⟩
    · push_neg at H
      exact ⟨0, Or.inr H⟩
  have : F1 = fun x ↦ if x ∈ m j then F0 j x else F0 (g (Nat.find (Z x))) x := by
    ext x
    have A : reparam x j = if x ∈ m j then j else g (Nat.find (Z x)) := rfl
    split_ifs with hjx
    · have : reparam x j = j := by rw [A, if_pos hjx]
      simp only [hF1, this]
    · have : reparam x j = g (Nat.find (Z x)) := by rw [A, if_neg hjx]
      simp only [hF1, this]
  rw [this]
  apply Measurable.piecewise (m_meas j) (F0_meas j)
  apply Measurable.find (fun n ↦ F0_meas (g n)) (fun n ↦ ?_)
  exact (m_meas (g n)).union mc_meas
@[deprecated (since := "2024-10-21")]
alias measurable_liminf' := Measurable.liminf'
theorem Measurable.limsup' {ι ι'} {f : ι → δ → α} {u : Filter ι} (hf : ∀ i, Measurable (f i))
    {p : ι' → Prop} {s : ι' → Set ι} (hu : u.HasCountableBasis p s) (hs : ∀ i, (s i).Countable) :
    Measurable fun x => limsup (fun i => f i x) u :=
  .liminf' (α := αᵒᵈ) hf hu hs
@[deprecated (since := "2024-10-21")]
alias measurable_limsup' := Measurable.limsup'
@[measurability]
theorem Measurable.liminf {f : ℕ → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun x => liminf (fun i => f i x) atTop :=
  .liminf' hf atTop_countable_basis fun _ => to_countable _
@[deprecated (since := "2024-10-21")]
alias measurable_liminf := Measurable.liminf
@[measurability]
theorem Measurable.limsup {f : ℕ → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun x => limsup (fun i => f i x) atTop :=
  .limsup' hf atTop_countable_basis fun _ => to_countable _
@[deprecated (since := "2024-10-21")]
alias measurable_limsup := Measurable.limsup
end ConditionallyCompleteLinearOrder
def Homemorph.toMeasurableEquiv (h : α ≃ₜ β) : α ≃ᵐ β where
  toEquiv := h.toEquiv
  measurable_toFun := h.continuous_toFun.measurable
  measurable_invFun := h.continuous_invFun.measurable
protected theorem IsFiniteMeasureOnCompacts.map (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (f : α ≃ₜ β) : IsFiniteMeasureOnCompacts (Measure.map f μ) := by
  refine ⟨fun K hK ↦ ?_⟩
  rw [← Homeomorph.toMeasurableEquiv_coe, MeasurableEquiv.map_apply]
  exact IsCompact.measure_lt_top (f.isCompact_preimage.2 hK)
end BorelSpace
section ENNReal
theorem measure_eq_measure_preimage_add_measure_tsum_Ico_zpow {α : Type*} {mα : MeasurableSpace α}
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} (hs : MeasurableSet s)
    {t : ℝ≥0} (ht : 1 < t) :
    μ s =
      μ (s ∩ f ⁻¹' {0}) + μ (s ∩ f ⁻¹' {∞}) +
      ∑' n : ℤ, μ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
  have A : μ s = μ (s ∩ f ⁻¹' {0}) + μ (s ∩ f ⁻¹' Ioi 0) := by
    rw [← measure_union]
    · rw [← inter_union_distrib_left, ← preimage_union, singleton_union, Ioi_insert,
        ← _root_.bot_eq_zero, Ici_bot, preimage_univ, inter_univ]
    · exact disjoint_singleton_left.mpr not_mem_Ioi_self
        |>.preimage f |>.inter_right' s |>.inter_left' s
    · exact hs.inter (hf measurableSet_Ioi)
  have B : μ (s ∩ f ⁻¹' Ioi 0) = μ (s ∩ f ⁻¹' {∞}) + μ (s ∩ f ⁻¹' Ioo 0 ∞) := by
    rw [← measure_union]
    · rw [← inter_union_distrib_left]
      congr
      ext x
      simp only [mem_singleton_iff, mem_union, mem_Ioo, mem_Ioi, mem_preimage]
      obtain (H | H) : f x = ∞ ∨ f x < ∞ := eq_or_lt_of_le le_top
      · simp only [H, eq_self_iff_true, or_false, ENNReal.zero_lt_top, not_top_lt, and_false]
      · simp only [H, H.ne, and_true, false_or]
    · refine disjoint_left.2 fun x hx h'x => ?_
      have : f x < ∞ := h'x.2.2
      exact lt_irrefl _ (this.trans_le (le_of_eq hx.2.symm))
    · exact hs.inter (hf measurableSet_Ioo)
  have C : μ (s ∩ f ⁻¹' Ioo 0 ∞) =
      ∑' n : ℤ, μ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
    rw [← measure_iUnion,
      ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow (ENNReal.one_lt_coe_iff.2 ht) ENNReal.coe_ne_top,
      preimage_iUnion, inter_iUnion]
    · intro i j hij
      wlog h : i < j generalizing i j
      · exact (this hij.symm (hij.lt_or_lt.resolve_left h)).symm
      refine disjoint_left.2 fun x hx h'x => lt_irrefl (f x) ?_
      calc
        f x < (t : ℝ≥0∞) ^ (i + 1) := hx.2.2
        _ ≤ (t : ℝ≥0∞) ^ j := ENNReal.zpow_le_of_le (ENNReal.one_le_coe_iff.2 ht.le) h
        _ ≤ f x := h'x.2.1
    · intro n
      exact hs.inter (hf measurableSet_Ico)
  rw [A, B, C, add_assoc]
end ENNReal