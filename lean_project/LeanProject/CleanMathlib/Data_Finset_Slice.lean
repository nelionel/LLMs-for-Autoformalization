import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Antichain
import Mathlib.Order.Interval.Finset.Nat
open Finset Nat
variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}
namespace Set
variable {A B : Set (Finset α)} {s : Finset α} {r : ℕ}
def Sized (r : ℕ) (A : Set (Finset α)) : Prop := ∀ ⦃x⦄, x ∈ A → #x = r
theorem Sized.mono (h : A ⊆ B) (hB : B.Sized r) : A.Sized r := fun _x hx => hB <| h hx
@[simp] lemma sized_empty : (∅ : Set (Finset α)).Sized r := by simp [Sized]
@[simp] lemma sized_singleton : ({s} : Set (Finset α)).Sized r ↔ #s = r := by simp [Sized]
theorem sized_union : (A ∪ B).Sized r ↔ A.Sized r ∧ B.Sized r :=
  ⟨fun hA => ⟨hA.mono subset_union_left, hA.mono subset_union_right⟩, fun hA _x hx =>
    hx.elim (fun h => hA.1 h) fun h => hA.2 h⟩
alias ⟨_, sized.union⟩ := sized_union
@[simp]
theorem sized_iUnion {f : ι → Set (Finset α)} : (⋃ i, f i).Sized r ↔ ∀ i, (f i).Sized r := by
  simp_rw [Set.Sized, Set.mem_iUnion, forall_exists_index]
  exact forall_swap
theorem sized_iUnion₂ {f : ∀ i, κ i → Set (Finset α)} :
    (⋃ (i) (j), f i j).Sized r ↔ ∀ i j, (f i j).Sized r := by
 simp only [Set.sized_iUnion]
protected theorem Sized.isAntichain (hA : A.Sized r) : IsAntichain (· ⊆ ·) A :=
  fun _s hs _t ht h hst => h <| Finset.eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le
protected theorem Sized.subsingleton (hA : A.Sized 0) : A.Subsingleton :=
  subsingleton_of_forall_eq ∅ fun _s hs => card_eq_zero.1 <| hA hs
theorem Sized.subsingleton' [Fintype α] (hA : A.Sized (Fintype.card α)) : A.Subsingleton :=
  subsingleton_of_forall_eq Finset.univ fun s hs => s.card_eq_iff_eq_univ.1 <| hA hs
theorem Sized.empty_mem_iff (hA : A.Sized r) : ∅ ∈ A ↔ A = {∅} :=
  hA.isAntichain.bot_mem_iff
theorem Sized.univ_mem_iff [Fintype α] (hA : A.Sized r) : Finset.univ ∈ A ↔ A = {Finset.univ} :=
  hA.isAntichain.top_mem_iff
theorem sized_powersetCard (s : Finset α) (r : ℕ) : (powersetCard r s : Set (Finset α)).Sized r :=
  fun _t ht => (mem_powersetCard.1 ht).2
end Set
namespace Finset
section Sized
variable [Fintype α] {𝒜 : Finset (Finset α)} {s : Finset α} {r : ℕ}
theorem subset_powersetCard_univ_iff : 𝒜 ⊆ powersetCard r univ ↔ (𝒜 : Set (Finset α)).Sized r :=
  forall_congr' fun A => by rw [mem_powersetCard_univ, mem_coe]
alias ⟨_, _root_.Set.Sized.subset_powersetCard_univ⟩ := subset_powersetCard_univ_iff
theorem _root_.Set.Sized.card_le (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    #𝒜 ≤ (Fintype.card α).choose r := by
  rw [Fintype.card, ← card_powersetCard]
  exact card_le_card (subset_powersetCard_univ_iff.mpr h𝒜)
end Sized
section Slice
variable {𝒜 : Finset (Finset α)} {A A₁ A₂ : Finset α} {r r₁ r₂ : ℕ}
def slice (𝒜 : Finset (Finset α)) (r : ℕ) : Finset (Finset α) := {A ∈ 𝒜 | #A = r}
@[inherit_doc]
scoped[Finset] infixl:90 " # " => Finset.slice
theorem mem_slice : A ∈ 𝒜 # r ↔ A ∈ 𝒜 ∧ #A = r :=
  mem_filter
theorem slice_subset : 𝒜 # r ⊆ 𝒜 :=
  filter_subset _ _
theorem sized_slice : (𝒜 # r : Set (Finset α)).Sized r := fun _ => And.right ∘ mem_slice.mp
theorem eq_of_mem_slice (h₁ : A ∈ 𝒜 # r₁) (h₂ : A ∈ 𝒜 # r₂) : r₁ = r₂ :=
  (sized_slice h₁).symm.trans <| sized_slice h₂
theorem ne_of_mem_slice (h₁ : A₁ ∈ 𝒜 # r₁) (h₂ : A₂ ∈ 𝒜 # r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
  mt fun h => (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))
theorem pairwiseDisjoint_slice : (Set.univ : Set ℕ).PairwiseDisjoint (slice 𝒜) := fun _ _ _ _ hmn =>
  disjoint_filter.2 fun _s _hs hm hn => hmn <| hm.symm.trans hn
variable [Fintype α] (𝒜)
@[simp]
theorem biUnion_slice [DecidableEq α] : (Iic <| Fintype.card α).biUnion 𝒜.slice = 𝒜 :=
  Subset.antisymm (biUnion_subset.2 fun _r _ => slice_subset) fun s hs =>
    mem_biUnion.2 ⟨#s, mem_Iic.2 <| s.card_le_univ, mem_slice.2 <| ⟨hs, rfl⟩⟩
@[simp]
theorem sum_card_slice : ∑ r ∈ Iic (Fintype.card α), #(𝒜 # r) = #𝒜 := by
  letI := Classical.decEq α
  rw [← card_biUnion, biUnion_slice]
  exact Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)
end Slice
end Finset