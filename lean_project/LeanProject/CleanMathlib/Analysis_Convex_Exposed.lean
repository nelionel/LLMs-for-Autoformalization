import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.OrderClosed
open scoped Classical
open Affine
open Set
section PreorderSemiring
variable (𝕜 : Type*) {E : Type*} [TopologicalSpace 𝕜] [Semiring 𝕜] [Preorder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}
def IsExposed (A B : Set E) : Prop :=
  B.Nonempty → ∃ l : E →L[𝕜] 𝕜, B = { x ∈ A | ∀ y ∈ A, l y ≤ l x }
end PreorderSemiring
section OrderedRing
variable {𝕜 : Type*} {E : Type*} [TopologicalSpace 𝕜] [OrderedRing 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {l : E →L[𝕜] 𝕜} {A B C : Set E} {x : E}
def ContinuousLinearMap.toExposed (l : E →L[𝕜] 𝕜) (A : Set E) : Set E :=
  { x ∈ A | ∀ y ∈ A, l y ≤ l x }
theorem ContinuousLinearMap.toExposed.isExposed : IsExposed 𝕜 A (l.toExposed A) := fun _ => ⟨l, rfl⟩
theorem isExposed_empty : IsExposed 𝕜 A ∅ := fun ⟨_, hx⟩ => by
  exfalso
  exact hx
namespace IsExposed
protected theorem subset (hAB : IsExposed 𝕜 A B) : B ⊆ A := by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1
@[refl]
protected theorem refl (A : Set E) : IsExposed 𝕜 A A := fun ⟨_, _⟩ =>
  ⟨0, Subset.antisymm (fun _ hx => ⟨hx, fun _ _ => le_refl 0⟩) fun _ hx => hx.1⟩
protected theorem antisymm (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A) : A = B :=
  hA.subset.antisymm hB.subset
protected theorem mono (hC : IsExposed 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) : IsExposed 𝕜 B C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩) fun x hx =>
    ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩
theorem eq_inter_halfSpace' {A B : Set E} (hAB : IsExposed 𝕜 A B) (hB : B.Nonempty) :
    ∃ l : E →L[𝕜] 𝕜, ∃ a, B = { x ∈ A | a ≤ l x } := by
  obtain ⟨l, rfl⟩ := hAB hB
  obtain ⟨w, hw⟩ := hB
  exact ⟨l, l w, Subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx =>
    ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩
@[deprecated (since := "2024-11-12")] alias eq_inter_halfspace' := eq_inter_halfSpace'
theorem eq_inter_halfSpace [Nontrivial 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B) :
    ∃ l : E →L[𝕜] 𝕜, ∃ a, B = { x ∈ A | a ≤ l x } := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · refine ⟨0, 1, ?_⟩
    rw [eq_comm, eq_empty_iff_forall_not_mem]
    rintro x ⟨-, h⟩
    rw [ContinuousLinearMap.zero_apply] at h
    have : ¬(1 : 𝕜) ≤ 0 := not_le_of_lt zero_lt_one
    contradiction
  exact hAB.eq_inter_halfSpace' hB
@[deprecated (since := "2024-11-12")] alias eq_inter_halfspace := eq_inter_halfSpace
protected theorem inter [ContinuousAdd 𝕜] {A B C : Set E} (hB : IsExposed 𝕜 A B)
    (hC : IsExposed 𝕜 A C) : IsExposed 𝕜 A (B ∩ C) := by
  rintro ⟨w, hwB, hwC⟩
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
  refine ⟨l₁ + l₂, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
    exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
  rintro x ⟨hxA, hx⟩
  refine ⟨⟨hxA, fun y hy => ?_⟩, hxA, fun y hy => ?_⟩
  · exact
      (add_le_add_iff_right (l₂ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans (hx w hwB.1))
  · exact
      (add_le_add_iff_left (l₁ x)).1 (le_trans (add_le_add (hwB.2 x hxA) (hwC.2 y hy)) (hx w hwB.1))
theorem sInter [ContinuousAdd 𝕜] {F : Finset (Set E)} (hF : F.Nonempty)
    (hAF : ∀ B ∈ F, IsExposed 𝕜 A B) : IsExposed 𝕜 A (⋂₀ F) := by
  induction F using Finset.induction with
  | empty => exfalso; exact Finset.not_nonempty_empty hF
  | @insert C F _ hF' =>
    rw [Finset.coe_insert, sInter_insert]
    obtain rfl | hFnemp := F.eq_empty_or_nonempty
    · rw [Finset.coe_empty, sInter_empty, inter_univ]
      exact hAF C (Finset.mem_singleton_self C)
    · exact (hAF C (Finset.mem_insert_self C F)).inter
        (hF' hFnemp fun B hB => hAF B (Finset.mem_insert_of_mem hB))
theorem inter_left (hC : IsExposed 𝕜 A C) (hCB : C ⊆ B) : IsExposed 𝕜 (A ∩ B) C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩)
    fun x ⟨⟨hxC, _⟩, hx⟩ => ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩
theorem inter_right (hC : IsExposed 𝕜 B C) (hCA : C ⊆ A) : IsExposed 𝕜 (A ∩ B) C := by
  rw [inter_comm]
  exact hC.inter_left hCA
protected theorem isClosed [OrderClosedTopology 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B)
    (hA : IsClosed A) : IsClosed B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfSpace' hB
  exact hA.isClosed_le continuousOn_const l.continuous.continuousOn
protected theorem isCompact [OrderClosedTopology 𝕜] [T2Space E] {A B : Set E}
    (hAB : IsExposed 𝕜 A B) (hA : IsCompact A) : IsCompact B :=
  hA.of_isClosed_subset (hAB.isClosed hA.isClosed) hAB.subset
end IsExposed
variable (𝕜)
def Set.exposedPoints (A : Set E) : Set E :=
  { x ∈ A | ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) }
variable {𝕜}
theorem exposed_point_def :
    x ∈ A.exposedPoints 𝕜 ↔ x ∈ A ∧ ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) :=
  Iff.rfl
theorem exposedPoints_subset : A.exposedPoints 𝕜 ⊆ A := fun _ hx => hx.1
@[simp]
theorem exposedPoints_empty : (∅ : Set E).exposedPoints 𝕜 = ∅ :=
  subset_empty_iff.1 exposedPoints_subset
theorem mem_exposedPoints_iff_exposed_singleton : x ∈ A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x} := by
  use fun ⟨hxA, l, hl⟩ _ =>
    ⟨l,
      Eq.symm <|
        eq_singleton_iff_unique_mem.2
          ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
  rintro h
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl
  exact
    ⟨hl.1.1, l, fun y hy =>
      ⟨hl.1.2 y hy, fun hxy => hl.2 y ⟨hy, fun z hz => (hl.1.2 z hz).trans hxy⟩⟩⟩
end OrderedRing
section LinearOrderedRing
variable {𝕜 : Type*} {E : Type*} [TopologicalSpace 𝕜] [LinearOrderedRing 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}
namespace IsExposed
protected theorem convex (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) : Convex 𝕜 B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
  obtain ⟨l, rfl⟩ := hAB hB
  exact fun x₁ hx₁ x₂ hx₂ a b ha hb hab =>
    ⟨hA hx₁.1 hx₂.1 ha hb hab, fun y hy =>
      ((l.toLinearMap.concaveOn convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩
          ⟨mem_univ _, hx₂.2 y hy⟩ ha hb hab).2⟩
protected theorem isExtreme (hAB : IsExposed 𝕜 A B) : IsExtreme 𝕜 A B := by
  refine ⟨hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxB hx => ?_⟩
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩
  have hl : ConvexOn 𝕜 univ l := l.toLinearMap.convexOn convex_univ
  have hlx₁ := hxB.2 x₁ hx₁A
  have hlx₂ := hxB.2 x₂ hx₂A
  refine ⟨⟨hx₁A, fun y hy => ?_⟩, ⟨hx₂A, fun y hy => ?_⟩⟩
  · rw [hlx₁.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlx₂)]
    exact hxB.2 y hy
  · rw [hlx₂.antisymm (hl.le_right_of_left_le (mem_univ _) (mem_univ _) hx hlx₁)]
    exact hxB.2 y hy
end IsExposed
theorem exposedPoints_subset_extremePoints : A.exposedPoints 𝕜 ⊆ A.extremePoints 𝕜 := fun _ hx =>
  (mem_exposedPoints_iff_exposed_singleton.1 hx).isExtreme.mem_extremePoints
end LinearOrderedRing