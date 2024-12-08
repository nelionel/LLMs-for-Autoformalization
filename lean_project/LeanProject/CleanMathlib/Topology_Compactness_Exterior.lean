import Mathlib.Tactic.Peel
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Exterior
variable {X : Type*} [TopologicalSpace X] {s : Set X}
theorem IsCompact.exterior_iff : IsCompact (exterior s) ↔ IsCompact s := by
  simp only [isCompact_iff_finite_subcover]
  peel with ι U hUo
  simp only [(isOpen_iUnion hUo).exterior_subset,
    (isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hUo i).exterior_subset]
protected alias ⟨IsCompact.of_exterior, IsCompact.exterior⟩ := IsCompact.exterior_iff
@[deprecated IsCompact.exterior (since := "2024-09-18")]
lemma Set.Finite.isCompact_exterior (hs : s.Finite) : IsCompact (exterior s) :=
  hs.isCompact.exterior