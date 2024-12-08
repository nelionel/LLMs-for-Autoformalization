import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot
open Filter Finset
variable {α β M : Type*} [CommMonoid M]
@[to_additive "Let `f` and `g` be two maps to the same commutative additive monoid. This lemma gives
a sufficient condition for comparison of the filter `atTop.map (fun s ↦ ∑ b ∈ s, f b)` with
`atTop.map (fun s ↦ ∑ b ∈ s, g b)`. This is useful to compare the set of limit points of
`∑ b ∈ s, f b` as `s → atTop` with the similar set for `g`."]
theorem Filter.map_atTop_finset_prod_le_of_prod_eq {f : α → M} {g : β → M}
    (h_eq : ∀ u : Finset β,
      ∃ v : Finset α, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∏ x ∈ u', g x = ∏ b ∈ v', f b) :
    (atTop.map fun s : Finset α => ∏ b ∈ s, f b) ≤
      atTop.map fun s : Finset β => ∏ x ∈ s, g x := by
  classical
    refine ((atTop_basis.map _).le_basis_iff (atTop_basis.map _)).2 fun b _ => ?_
    let ⟨v, hv⟩ := h_eq b
    refine ⟨v, trivial, ?_⟩
    simpa [Finset.image_subset_iff] using hv
@[to_additive]
theorem Function.Injective.map_atTop_finset_prod_eq {g : α → β}
    (hg : Function.Injective g) {f : β → M} (hf : ∀ x, x ∉ Set.range g → f x = 1) :
    map (fun s => ∏ i ∈ s, f (g i)) atTop = map (fun s => ∏ i ∈ s, f i) atTop := by
  haveI := Classical.decEq β
  apply le_antisymm <;> refine map_atTop_finset_prod_le_of_prod_eq fun s => ?_
  · refine ⟨s.preimage g hg.injOn, fun t ht => ?_⟩
    refine ⟨t.image g ∪ s, Finset.subset_union_right, ?_⟩
    rw [← Finset.prod_image hg.injOn]
    refine (prod_subset subset_union_left ?_).symm
    simp only [Finset.mem_union, Finset.mem_image]
    refine fun y hy hyt => hf y (mt ?_ hyt)
    rintro ⟨x, rfl⟩
    exact ⟨x, ht (Finset.mem_preimage.2 <| hy.resolve_left hyt), rfl⟩
  · refine ⟨s.image g, fun t ht => ?_⟩
    simp only [← prod_preimage _ _ hg.injOn _ fun x _ => hf x]
    exact ⟨_, (image_subset_iff_subset_preimage _).1 ht, rfl⟩
add_decl_doc Function.Injective.map_atTop_finset_sum_eq