import Mathlib.Topology.GDelta.UniformSpace
import Mathlib.Topology.LocallyClosed
import Mathlib.MeasureTheory.Constructions.EventuallyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
variable (α : Type*) {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
open Topology
scoped[Topology] notation:50 f " =ᵇ " g:50 => Filter.EventuallyEq (residual _) f g
scoped[Topology] notation3 "∀ᵇ "(...)", "r:(scoped p => Filter.Eventually p <| residual _) => r
scoped[Topology] notation3 "∃ᵇ "(...)", "r:(scoped p => Filter.Frequently p <| residual _) => r
variable {α}
def BaireMeasurableSet (s : Set α) : Prop :=
  @MeasurableSet _ (EventuallyMeasurableSpace (borel _) (residual _)) s
variable {s t : Set α}
namespace BaireMeasurableSet
theorem of_mem_residual (h : s ∈ residual _) : BaireMeasurableSet s :=
  eventuallyMeasurableSet_of_mem_filter (α := α) h
theorem _root_.MeasurableSet.baireMeasurableSet [MeasurableSpace α] [BorelSpace α]
    (h : MeasurableSet s) : BaireMeasurableSet s := by
  borelize α
  exact h.eventuallyMeasurableSet
theorem _root_.IsOpen.baireMeasurableSet (h : IsOpen s) : BaireMeasurableSet s := by
  borelize α
  exact h.measurableSet.baireMeasurableSet
theorem compl (h : BaireMeasurableSet s) : BaireMeasurableSet sᶜ := MeasurableSet.compl h
theorem of_compl (h : BaireMeasurableSet sᶜ) : BaireMeasurableSet s := MeasurableSet.of_compl h
theorem _root_.IsMeagre.baireMeasurableSet (h : IsMeagre s) : BaireMeasurableSet s :=
  (of_mem_residual h).of_compl
theorem iUnion {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i, s i) :=
  MeasurableSet.iUnion h
theorem biUnion {ι : Type*}  {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i ∈ t, s i) :=
  MeasurableSet.biUnion ht h
theorem sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs h
theorem iInter {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i, s i) :=
  MeasurableSet.iInter h
theorem biInter {ι : Type*}  {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i ∈ t, s i) :=
  MeasurableSet.biInter ht h
theorem sInter {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs h
theorem union (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∪ t) :=
  MeasurableSet.union hs ht
theorem inter (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∩ t) :=
  MeasurableSet.inter hs ht
theorem diff (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s \ t) :=
  MeasurableSet.diff hs ht
theorem congr (hs : BaireMeasurableSet s) (h : s =ᵇ t) : BaireMeasurableSet t :=
  EventuallyMeasurableSet.congr (α := α) hs h.symm
end BaireMeasurableSet
open Filter
theorem MeasurableSet.residualEq_isOpen [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s) :
    ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  apply h.induction_on_open (fun s hs => ⟨s, hs, EventuallyEq.rfl⟩)
  · rintro s - ⟨u, uo, su⟩
    refine ⟨(closure u)ᶜ, isClosed_closure.isOpen_compl,
      EventuallyEq.compl (su.trans <| EventuallyLE.antisymm subset_closure.eventuallyLE ?_)⟩
    have : (coborder u) ∈ residual _ :=
      residual_of_dense_open uo.isLocallyClosed.isOpen_coborder dense_coborder
    rw [coborder_eq_union_closure_compl] at this
    rw [EventuallyLE]
    convert this
    simp only [le_Prop_eq, imp_iff_or_not]
    rfl 
  rintro s - - hs
  choose u uo su using hs
  exact ⟨⋃ i, u i, isOpen_iUnion uo, EventuallyEq.countable_iUnion su⟩
theorem BaireMeasurableSet.residualEq_isOpen (h : BaireMeasurableSet s) :
    ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_isOpen with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩
theorem BaireMeasurableSet.iff_residualEq_isOpen :
    BaireMeasurableSet s ↔ ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u :=
  ⟨fun h => h.residualEq_isOpen , fun ⟨_, uo, ueq⟩ => uo.baireMeasurableSet.congr ueq.symm⟩
section Map
open Set
variable {f : α → β}
theorem tendsto_residual_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f) :
    Tendsto f (residual α) (residual β) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro t ⟨ht, htd⟩
  exact residual_of_dense_open (ht.preimage hc) (htd.preimage ho)
theorem IsMeagre.preimage_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : IsMeagre s) : IsMeagre (f ⁻¹' s) :=
  tendsto_residual_of_isOpenMap hc ho h
theorem BaireMeasurableSet.preimage (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : BaireMeasurableSet s) : BaireMeasurableSet (f⁻¹' s) := by
  rcases h with ⟨u, hu, hsu⟩
  refine ⟨f ⁻¹' u, ?_, hsu.filter_mono <| tendsto_residual_of_isOpenMap hc ho⟩
  borelize α β
  exact hc.measurable hu
theorem Homeomorph.residual_map_eq (h : α ≃ₜ β) : (residual α).map h = residual β := by
  refine le_antisymm (tendsto_residual_of_isOpenMap h.continuous h.isOpenMap) (le_map ?_)
  simp_rw [← preimage_symm]
  exact tendsto_residual_of_isOpenMap h.symm.continuous h.symm.isOpenMap
end Map