import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
open Finset Set
variable (𝕜 E : Type*) [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
namespace Geometry
@[ext]
structure SimplicialComplex where
  faces : Set (Finset E)
  not_empty_mem : ∅ ∉ faces
  indep : ∀ {s}, s ∈ faces → AffineIndependent 𝕜 ((↑) : s → E)
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces
  inter_subset_convexHull : ∀ {s t}, s ∈ faces → t ∈ faces →
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)
namespace SimplicialComplex
variable {𝕜 E}
variable {K : SimplicialComplex 𝕜 E} {s t : Finset E} {x : E}
instance : Membership (Finset E) (SimplicialComplex 𝕜 E) :=
  ⟨fun K s => s ∈ K.faces⟩
def space (K : SimplicialComplex 𝕜 E) : Set E :=
  ⋃ s ∈ K.faces, convexHull 𝕜 (s : Set E)
theorem mem_space_iff : x ∈ K.space ↔ ∃ s ∈ K.faces, x ∈ convexHull 𝕜 (s : Set E) := by
  simp [space]
theorem convexHull_subset_space (hs : s ∈ K.faces) : convexHull 𝕜 ↑s ⊆ K.space := by
  convert subset_biUnion_of_mem hs
  rfl
protected theorem subset_space (hs : s ∈ K.faces) : (s : Set E) ⊆ K.space :=
  (subset_convexHull 𝕜 _).trans <| convexHull_subset_space hs
theorem convexHull_inter_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t = convexHull 𝕜 (s ∩ t : Set E) :=
  (K.inter_subset_convexHull hs ht).antisymm <|
    subset_inter (convexHull_mono Set.inter_subset_left) <|
      convexHull_mono Set.inter_subset_right
theorem disjoint_or_exists_inter_eq_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    Disjoint (convexHull 𝕜 (s : Set E)) (convexHull 𝕜 ↑t) ∨
      ∃ u ∈ K.faces, convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 ↑t = convexHull 𝕜 ↑u := by
  classical
  by_contra! h
  refine h.2 (s ∩ t) (K.down_closed hs inter_subset_left fun hst => h.1 <|
    disjoint_iff_inf_le.mpr <| (K.inter_subset_convexHull hs ht).trans ?_) ?_
  · rw [← coe_inter, hst, coe_empty, convexHull_empty]
    rfl
  · rw [coe_inter, convexHull_inter_convexHull hs ht]
@[simps]
def ofErase (faces : Set (Finset E)) (indep : ∀ s ∈ faces, AffineIndependent 𝕜 ((↑) : s → E))
    (down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces)
    (inter_subset_convexHull : ∀ᵉ (s ∈ faces) (t ∈ faces),
      convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)) :
    SimplicialComplex 𝕜 E where
  faces := faces \ {∅}
  not_empty_mem h := h.2 (mem_singleton _)
  indep hs := indep _ hs.1
  down_closed hs hts ht := ⟨down_closed _ hs.1 _ hts, ht⟩
  inter_subset_convexHull hs ht := inter_subset_convexHull _ hs.1 _ ht.1
@[simps]
def ofSubcomplex (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces ⊆ K.faces)
    (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces) : SimplicialComplex 𝕜 E :=
  { faces
    not_empty_mem := fun h => K.not_empty_mem (subset h)
    indep := fun hs => K.indep (subset hs)
    down_closed := fun hs hts _ => down_closed hs hts
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull (subset hs) (subset ht) }
def vertices (K : SimplicialComplex 𝕜 E) : Set E :=
  { x | {x} ∈ K.faces }
theorem mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := Iff.rfl
theorem vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : Set E) := by
  ext x
  refine ⟨fun h => mem_biUnion h <| mem_coe.2 <| mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_ne_empty _)
theorem vertices_subset_space : K.vertices ⊆ K.space :=
  vertices_eq.subset.trans <| iUnion₂_mono fun x _ => subset_convexHull 𝕜 (x : Set E)
theorem vertex_mem_convexHull_iff (hx : x ∈ K.vertices) (hs : s ∈ K.faces) :
    x ∈ convexHull 𝕜 (s : Set E) ↔ x ∈ s := by
  refine ⟨fun h => ?_, fun h => subset_convexHull 𝕜 _ h⟩
  classical
  have h := K.inter_subset_convexHull hx hs ⟨by simp, h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm,
    coe_empty, convexHull_empty] at h
theorem face_subset_face_iff (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t ↔ s ⊆ t :=
  ⟨fun h _ hxs =>
    (vertex_mem_convexHull_iff
          (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_ne_empty _) ht).1
      (h (subset_convexHull 𝕜 (E := E) s hxs)),
    convexHull_mono⟩
def facets (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  { s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t }
theorem mem_facets : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t :=
  mem_sep_iff
theorem facets_subset : K.facets ⊆ K.faces := fun _ hs => hs.1
theorem not_facet_iff_subface (hs : s ∈ K.faces) : s ∉ K.facets ↔ ∃ t, t ∈ K.faces ∧ s ⊂ t := by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push_neg at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Subset.refl t)
variable (𝕜 E)
instance : Min (SimplicialComplex 𝕜 E) :=
  ⟨fun K L =>
    { faces := K.faces ∩ L.faces
      not_empty_mem := fun h => K.not_empty_mem (Set.inter_subset_left h)
      indep := fun hs => K.indep hs.1
      down_closed := fun hs hst ht => ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }⟩
instance : SemilatticeInf (SimplicialComplex 𝕜 E) :=
  { PartialOrder.lift faces (fun _ _ => SimplicialComplex.ext) with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }
instance hasBot : Bot (SimplicialComplex 𝕜 E) :=
  ⟨{  faces := ∅
      not_empty_mem := Set.not_mem_empty ∅
      indep := fun hs => (Set.not_mem_empty _ hs).elim
      down_closed := fun hs => (Set.not_mem_empty _ hs).elim
      inter_subset_convexHull := fun hs => (Set.not_mem_empty _ hs).elim }⟩
instance : OrderBot (SimplicialComplex 𝕜 E) :=
  { SimplicialComplex.hasBot 𝕜 E with bot_le := fun _ => Set.empty_subset _ }
instance : Inhabited (SimplicialComplex 𝕜 E) :=
  ⟨⊥⟩
variable {𝕜 E}
theorem faces_bot : (⊥ : SimplicialComplex 𝕜 E).faces = ∅ := rfl
theorem space_bot : (⊥ : SimplicialComplex 𝕜 E).space = ∅ :=
  Set.biUnion_empty _
theorem facets_bot : (⊥ : SimplicialComplex 𝕜 E).facets = ∅ :=
  eq_empty_of_subset_empty facets_subset
end SimplicialComplex
end Geometry