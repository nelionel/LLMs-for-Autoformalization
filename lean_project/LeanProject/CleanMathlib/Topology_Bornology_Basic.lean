import Mathlib.Order.Filter.Cofinite
open Set Filter
variable {ι α β : Type*}
class Bornology (α : Type*) where
  cobounded' : Filter α
  le_cofinite' : cobounded' ≤ cofinite
def Bornology.cobounded (α : Type*) [Bornology α] : Filter α := Bornology.cobounded'
alias Bornology.Simps.cobounded := Bornology.cobounded
lemma Bornology.le_cofinite (α : Type*) [Bornology α] : cobounded α ≤ cofinite :=
Bornology.le_cofinite'
initialize_simps_projections Bornology (cobounded' → cobounded)
@[ext]
lemma Bornology.ext (t t' : Bornology α)
    (h_cobounded : @Bornology.cobounded α t = @Bornology.cobounded α t') :
    t = t' := by
  cases t
  cases t'
  congr
@[simps]
def Bornology.ofBounded {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ ⊆ s₁, s₂ ∈ B)
    (union_mem : ∀ s₁ ∈ B, ∀ s₂ ∈ B, s₁ ∪ s₂ ∈ B)
    (singleton_mem : ∀ x, {x} ∈ B) : Bornology α where
  cobounded' := comk (· ∈ B) empty_mem subset_mem union_mem
  le_cofinite' := by simpa [le_cofinite_iff_compl_singleton_mem]
@[simps! cobounded]
def Bornology.ofBounded' {α : Type*} (B : Set (Set α))
    (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ ⊆ s₁, s₂ ∈ B)
    (union_mem : ∀ s₁ ∈ B, ∀ s₂ ∈ B, s₁ ∪ s₂ ∈ B)
    (sUnion_univ : ⋃₀ B = univ) :
    Bornology α :=
  Bornology.ofBounded B empty_mem subset_mem union_mem fun x => by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)
namespace Bornology
section
def IsCobounded [Bornology α] (s : Set α) : Prop :=
  s ∈ cobounded α
def IsBounded [Bornology α] (s : Set α) : Prop :=
  IsCobounded sᶜ
variable {_ : Bornology α} {s t : Set α} {x : α}
theorem isCobounded_def {s : Set α} : IsCobounded s ↔ s ∈ cobounded α :=
  Iff.rfl
theorem isBounded_def {s : Set α} : IsBounded s ↔ sᶜ ∈ cobounded α :=
  Iff.rfl
@[simp]
theorem isBounded_compl_iff : IsBounded sᶜ ↔ IsCobounded s := by
  rw [isBounded_def, isCobounded_def, compl_compl]
@[simp]
theorem isCobounded_compl_iff : IsCobounded sᶜ ↔ IsBounded s :=
  Iff.rfl
alias ⟨IsBounded.of_compl, IsCobounded.compl⟩ := isBounded_compl_iff
alias ⟨IsCobounded.of_compl, IsBounded.compl⟩ := isCobounded_compl_iff
@[simp]
theorem isBounded_empty : IsBounded (∅ : Set α) := by
  rw [isBounded_def, compl_empty]
  exact univ_mem
theorem nonempty_of_not_isBounded (h : ¬IsBounded s) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact h isBounded_empty
@[simp]
theorem isBounded_singleton : IsBounded ({x} : Set α) := by
  rw [isBounded_def]
  exact le_cofinite _ (finite_singleton x).compl_mem_cofinite
theorem isBounded_iff_forall_mem : IsBounded s ↔ ∀ x ∈ s, IsBounded s :=
  ⟨fun h _ _ ↦ h, fun h ↦ by
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    exacts [isBounded_empty, h x hx]⟩
@[simp]
theorem isCobounded_univ : IsCobounded (univ : Set α) :=
  univ_mem
@[simp]
theorem isCobounded_inter : IsCobounded (s ∩ t) ↔ IsCobounded s ∧ IsCobounded t :=
  inter_mem_iff
theorem IsCobounded.inter (hs : IsCobounded s) (ht : IsCobounded t) : IsCobounded (s ∩ t) :=
  isCobounded_inter.2 ⟨hs, ht⟩
@[simp]
theorem isBounded_union : IsBounded (s ∪ t) ↔ IsBounded s ∧ IsBounded t := by
  simp only [← isCobounded_compl_iff, compl_union, isCobounded_inter]
theorem IsBounded.union (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ∪ t) :=
  isBounded_union.2 ⟨hs, ht⟩
theorem IsCobounded.superset (hs : IsCobounded s) (ht : s ⊆ t) : IsCobounded t :=
  mem_of_superset hs ht
theorem IsBounded.subset (ht : IsBounded t) (hs : s ⊆ t) : IsBounded s :=
  ht.superset (compl_subset_compl.mpr hs)
@[simp]
theorem sUnion_bounded_univ : ⋃₀ { s : Set α | IsBounded s } = univ :=
  sUnion_eq_univ_iff.2 fun a => ⟨{a}, isBounded_singleton, mem_singleton a⟩
theorem IsBounded.insert (h : IsBounded s) (x : α) : IsBounded (insert x s) :=
  isBounded_singleton.union h
@[simp]
theorem isBounded_insert : IsBounded (insert x s) ↔ IsBounded s :=
  ⟨fun h ↦ h.subset (subset_insert _ _), (.insert · x)⟩
theorem comap_cobounded_le_iff [Bornology β] {f : α → β} :
    (cobounded β).comap f ≤ cobounded α ↔ ∀ ⦃s⦄, IsBounded s → IsBounded (f '' s) := by
  refine
    ⟨fun h s hs => ?_, fun h t ht =>
      ⟨(f '' tᶜ)ᶜ, h <| IsCobounded.compl ht, compl_subset_comm.1 <| subset_preimage_image _ _⟩⟩
  obtain ⟨t, ht, hts⟩ := h hs.compl
  rw [subset_compl_comm, ← preimage_compl] at hts
  exact (IsCobounded.compl ht).subset ((image_subset f hts).trans <| image_preimage_subset _ _)
end
theorem ext_iff' {t t' : Bornology α} :
    t = t' ↔ ∀ s, s ∈ @cobounded α t ↔ s ∈ @cobounded α t' :=
  Bornology.ext_iff.trans Filter.ext_iff
theorem ext_iff_isBounded {t t' : Bornology α} :
    t = t' ↔ ∀ s, @IsBounded α t s ↔ @IsBounded α t' s :=
  ext_iff'.trans compl_surjective.forall
variable {s : Set α}
theorem isCobounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsCobounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ sᶜ ∈ B :=
  Iff.rfl
theorem isBounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsBounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ s ∈ B := by
  rw [isBounded_def, ofBounded_cobounded, compl_mem_comk]
variable [Bornology α]
theorem isCobounded_biInter {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_mem hs
@[simp]
theorem isCobounded_biInter_finset (s : Finset ι) {f : ι → Set α} :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_finset_mem s
@[simp]
theorem isCobounded_iInter [Finite ι] {f : ι → Set α} :
    IsCobounded (⋂ i, f i) ↔ ∀ i, IsCobounded (f i) :=
  iInter_mem
theorem isCobounded_sInter {S : Set (Set α)} (hs : S.Finite) :
    IsCobounded (⋂₀ S) ↔ ∀ s ∈ S, IsCobounded s :=
  sInter_mem hs
theorem isBounded_biUnion {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) := by
  simp only [← isCobounded_compl_iff, compl_iUnion, isCobounded_biInter hs]
theorem isBounded_biUnion_finset (s : Finset ι) {f : ι → Set α} :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) :=
  isBounded_biUnion s.finite_toSet
theorem isBounded_sUnion {S : Set (Set α)} (hs : S.Finite) :
    IsBounded (⋃₀ S) ↔ ∀ s ∈ S, IsBounded s := by rw [sUnion_eq_biUnion, isBounded_biUnion hs]
@[simp]
theorem isBounded_iUnion [Finite ι] {s : ι → Set α} :
    IsBounded (⋃ i, s i) ↔ ∀ i, IsBounded (s i) := by
  rw [← sUnion_range, isBounded_sUnion (finite_range s), forall_mem_range]
lemma eventually_ne_cobounded (a : α) : ∀ᶠ x in cobounded α, x ≠ a :=
  le_cofinite_iff_eventually_ne.1 (le_cofinite _) a
end Bornology
open Bornology
theorem Filter.HasBasis.disjoint_cobounded_iff [Bornology α] {ι : Sort*} {p : ι → Prop}
    {s : ι → Set α} {l : Filter α} (h : l.HasBasis p s) :
    Disjoint l (cobounded α) ↔ ∃ i, p i ∧ Bornology.IsBounded (s i) :=
  h.disjoint_iff_left
theorem Set.Finite.isBounded [Bornology α] {s : Set α} (hs : s.Finite) : IsBounded s :=
  Bornology.le_cofinite α hs.compl_mem_cofinite
nonrec lemma Filter.Tendsto.eventually_ne_cobounded [Bornology α] {f : β → α} {l : Filter β}
    (h : Tendsto f l (cobounded α)) (a : α) : ∀ᶠ x in l, f x ≠ a :=
  h.eventually <| eventually_ne_cobounded a
instance : Bornology PUnit :=
  ⟨⊥, bot_le⟩
abbrev Bornology.cofinite : Bornology α where
  cobounded' := Filter.cofinite
  le_cofinite' := le_rfl
class BoundedSpace (α : Type*) [Bornology α] : Prop where
  bounded_univ : Bornology.IsBounded (univ : Set α)
instance (priority := 100) BoundedSpace.of_finite {α : Type*} [Bornology α] [Finite α] :
    BoundedSpace α where
  bounded_univ := (toFinite _).isBounded
namespace Bornology
variable [Bornology α]
theorem isBounded_univ : IsBounded (univ : Set α) ↔ BoundedSpace α :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
theorem cobounded_eq_bot_iff : cobounded α = ⊥ ↔ BoundedSpace α := by
  rw [← isBounded_univ, isBounded_def, compl_univ, empty_mem_iff_bot]
variable [BoundedSpace α]
theorem IsBounded.all (s : Set α) : IsBounded s :=
  BoundedSpace.bounded_univ.subset s.subset_univ
theorem IsCobounded.all (s : Set α) : IsCobounded s :=
  compl_compl s ▸ IsBounded.all sᶜ
variable (α)
@[simp]
theorem cobounded_eq_bot : cobounded α = ⊥ :=
  cobounded_eq_bot_iff.2 ‹_›
end Bornology
namespace OrderDual
variable [Bornology α]
instance instBornology : Bornology αᵒᵈ := ‹Bornology α›
@[simp] lemma isCobounded_preimage_ofDual {s : Set α} :
    IsCobounded (ofDual ⁻¹' s) ↔ IsCobounded s := Iff.rfl
@[simp] lemma isCobounded_preimage_toDual {s : Set αᵒᵈ} :
    IsCobounded (toDual ⁻¹' s) ↔ IsCobounded s := Iff.rfl
@[simp] lemma isBounded_preimage_ofDual {s : Set α} :
    IsBounded (ofDual ⁻¹' s) ↔ IsBounded s := Iff.rfl
@[simp] lemma isBounded_preimage_toDual {s : Set αᵒᵈ} :
    IsBounded (toDual ⁻¹' s) ↔ IsBounded s := Iff.rfl
end OrderDual