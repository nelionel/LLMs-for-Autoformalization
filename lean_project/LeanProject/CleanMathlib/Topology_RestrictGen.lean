import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.Compactness.Compact
open Filter Set
variable {X : Type*} [TopologicalSpace X] {S : Set (Set X)} {t : Set X} {x : X}
namespace Topology.RestrictGenTopology
protected theorem isOpen_iff (hS : RestrictGenTopology S) :
    IsOpen t ↔ ∀ s ∈ S, IsOpen ((↑) ⁻¹' t : Set s) :=
  ⟨fun ht _ _ ↦ ht.preimage continuous_subtype_val, hS.1 t⟩
protected theorem isClosed_iff (hS : RestrictGenTopology S) :
    IsClosed t ↔ ∀ s ∈ S, IsClosed ((↑) ⁻¹' t : Set s) := by
  simp only [← isOpen_compl_iff, hS.isOpen_iff, preimage_compl]
protected theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hS : RestrictGenTopology S) :
    Continuous f ↔ ∀ s ∈ S, ContinuousOn f s :=
  ⟨fun h _ _ ↦ h.continuousOn, fun h ↦ continuous_def.2 fun _u hu ↦ hS.isOpen_iff.2 fun s hs ↦
    hu.preimage <| (h s hs).restrict⟩
theorem of_continuous_prop (h : ∀ f : X → Prop, (∀ s ∈ S, ContinuousOn f s) → Continuous f) :
    RestrictGenTopology S where
  isOpen_of_forall_induced u hu := by
    simp only [continuousOn_iff_continuous_restrict, continuous_Prop] at *
    exact h _ hu
theorem of_isClosed (h : ∀ t : Set X, (∀ s ∈ S, IsClosed ((↑) ⁻¹' t : Set s)) → IsClosed t) :
    RestrictGenTopology S :=
  ⟨fun _t ht ↦ isClosed_compl_iff.1 <| h _ fun s hs ↦ (ht s hs).isClosed_compl⟩
protected theorem enlarge {T} (hS : RestrictGenTopology S) (hT : ∀ s ∈ S, ∃ t ∈ T, s ⊆ t) :
    RestrictGenTopology T :=
  of_continuous_prop fun _f hf ↦ hS.continuous_iff.2 fun s hs ↦
    let ⟨t, htT, hst⟩ := hT s hs; (hf t htT).mono hst
protected theorem mono {T} (hS : RestrictGenTopology S) (hT : S ⊆ T) : RestrictGenTopology T :=
  hS.enlarge fun s hs ↦ ⟨s, hT hs, Subset.rfl⟩
lemma of_seq [SequentialSpace X]
    (h : ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) → insert x (range u) ∈ S) :
    RestrictGenTopology S := by
  refine of_isClosed fun t ht ↦ IsSeqClosed.isClosed fun u x hut hux ↦ ?_
  rcases isClosed_induced_iff.1 (ht _ (h hux)) with ⟨s, hsc, hst⟩
  rw [Subtype.preimage_val_eq_preimage_val_iff, Set.ext_iff] at hst
  suffices x ∈ s by specialize hst x; simp_all
  refine hsc.mem_of_tendsto hux <| Eventually.of_forall fun k ↦ ?_
  specialize hst (u k)
  simp_all
lemma isCompact_of_seq [SequentialSpace X] : RestrictGenTopology {K : Set X | IsCompact K} :=
  of_seq fun _u _x hux ↦ hux.isCompact_insert_range
lemma of_nhds (h : ∀ x, ∃ s ∈ S, s ∈ 𝓝 x) : RestrictGenTopology S :=
  of_continuous_prop fun _f hf ↦ continuous_iff_continuousAt.2 fun x ↦
    let ⟨s, hsS, hsx⟩ := h x
    (hf s hsS).continuousAt hsx
lemma isCompact_of_weaklyLocallyCompact [WeaklyLocallyCompactSpace X] :
    RestrictGenTopology {K : Set X | IsCompact K} :=
  of_nhds exists_compact_mem_nhds
end Topology.RestrictGenTopology