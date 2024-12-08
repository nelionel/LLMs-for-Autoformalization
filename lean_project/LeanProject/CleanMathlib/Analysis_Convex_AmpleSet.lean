import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.AffineSpace.ContinuousAffineEquiv
open Set
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
def AmpleSet (s : Set F) : Prop :=
  ∀ x ∈ s, convexHull ℝ (connectedComponentIn s x) = univ
@[simp]
theorem ampleSet_univ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AmpleSet (univ : Set F) := by
  intro x _
  rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]
@[simp]
theorem ampleSet_empty : AmpleSet (∅ : Set F) := fun _ ↦ False.elim
namespace AmpleSet
theorem union {s t : Set F} (hs : AmpleSet s) (ht : AmpleSet t) : AmpleSet (s ∪ t) := by
  intro x hx
  rcases hx with (h | h) <;>
  [have hx := hs x h; have hx := ht x h] <;>
  rw [← Set.univ_subset_iff, ← hx] <;>
  apply convexHull_mono <;>
  apply connectedComponentIn_mono <;>
  [apply subset_union_left; apply subset_union_right]
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
theorem image {s : Set E} (h : AmpleSet s) (L : E ≃ᵃL[ℝ] F) :
    AmpleSet (L '' s) := forall_mem_image.mpr fun x hx ↦
  calc (convexHull ℝ) (connectedComponentIn (L '' s) (L x))
    _ = (convexHull ℝ) (L '' (connectedComponentIn s x)) :=
          .symm <| congrArg _ <| L.toHomeomorph.image_connectedComponentIn hx
    _ = L '' (convexHull ℝ (connectedComponentIn s x)) :=
          .symm <| L.toAffineMap.image_convexHull _
    _ = univ := by rw [h x hx, image_univ, L.surjective.range_eq]
theorem image_iff {s : Set E} (L : E ≃ᵃL[ℝ] F) :
    AmpleSet (L '' s) ↔ AmpleSet s :=
  ⟨fun h ↦ (L.symm_image_image s) ▸ h.image L.symm, fun h ↦ h.image L⟩
theorem preimage {s : Set F} (h : AmpleSet s) (L : E ≃ᵃL[ℝ] F) : AmpleSet (L ⁻¹' s) := by
  rw [← L.image_symm_eq_preimage]
  exact h.image L.symm
theorem preimage_iff {s : Set F} (L : E ≃ᵃL[ℝ] F) :
    AmpleSet (L ⁻¹' s) ↔ AmpleSet s :=
  ⟨fun h ↦ L.image_preimage s ▸ h.image L, fun h ↦ h.preimage L⟩
open scoped Pointwise
theorem vadd [ContinuousAdd E] {s : Set E} (h : AmpleSet s) {y : E} :
    AmpleSet (y +ᵥ s) :=
  h.image (ContinuousAffineEquiv.constVAdd ℝ E y)
theorem vadd_iff [ContinuousAdd E] {s : Set E} {y : E} :
    AmpleSet (y +ᵥ s) ↔ AmpleSet s :=
  AmpleSet.image_iff (ContinuousAffineEquiv.constVAdd ℝ E y)
section Codimension
theorem of_one_lt_codim [TopologicalAddGroup F] [ContinuousSMul ℝ F] {E : Submodule ℝ F}
    (hcodim : 1 < Module.rank ℝ (F ⧸ E)) :
    AmpleSet (Eᶜ : Set F) := fun x hx ↦ by
  rw [E.connectedComponentIn_eq_self_of_one_lt_codim hcodim hx, eq_univ_iff_forall]
  intro y
  by_cases h : y ∈ E
  · obtain ⟨z, hz⟩ : ∃ z, z ∉ E := by
      rw [← not_forall, ← Submodule.eq_top_iff']
      rintro rfl
      simp [rank_zero_iff.2 inferInstance] at hcodim
    refine segment_subset_convexHull ?_ ?_ (mem_segment_sub_add y z) <;>
      simpa [sub_eq_add_neg, Submodule.add_mem_iff_right _ h]
  · exact subset_convexHull ℝ (Eᶜ : Set F) h
end Codimension
end AmpleSet