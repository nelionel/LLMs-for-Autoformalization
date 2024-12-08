import Mathlib.Order.Filter.Tendsto
import Mathlib.Data.PFun
universe u v w
namespace Filter
variable {α : Type u} {β : Type v} {γ : Type w}
open Filter
def rmap (r : Rel α β) (l : Filter α) : Filter β where
  sets := { s | r.core s ∈ l }
  univ_sets := by simp
  sets_of_superset hs st := mem_of_superset hs (Rel.core_mono _ st)
  inter_sets hs ht := by
    simp only [Set.mem_setOf_eq]
    convert inter_mem hs ht
    rw [← Rel.core_inter]
theorem rmap_sets (r : Rel α β) (l : Filter α) : (l.rmap r).sets = r.core ⁻¹' l.sets :=
  rfl
@[simp]
theorem mem_rmap (r : Rel α β) (l : Filter α) (s : Set β) : s ∈ l.rmap r ↔ r.core s ∈ l :=
  Iff.rfl
@[simp]
theorem rmap_rmap (r : Rel α β) (s : Rel β γ) (l : Filter α) :
    rmap s (rmap r l) = rmap (r.comp s) l :=
  filter_eq <| by simp [rmap_sets, Set.preimage, Rel.core_comp]
@[simp]
theorem rmap_compose (r : Rel α β) (s : Rel β γ) : rmap s ∘ rmap r = rmap (r.comp s) :=
  funext <| rmap_rmap _ _
def RTendsto (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.rmap r ≤ l₂
theorem rtendsto_def (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ ∀ s ∈ l₂, r.core s ∈ l₁ :=
  Iff.rfl
def rcomap (r : Rel α β) (f : Filter β) : Filter α where
  sets := Rel.image (fun s t => r.core s ⊆ t) f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, (r.core_inter a' b').subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩
theorem rcomap_sets (r : Rel α β) (f : Filter β) :
    (rcomap r f).sets = Rel.image (fun s t => r.core s ⊆ t) f.sets :=
  rfl
theorem rcomap_rcomap (r : Rel α β) (s : Rel β γ) (l : Filter γ) :
    rcomap r (rcomap s l) = rcomap (r.comp s) l :=
  filter_eq <| by
    ext t; simp only [rcomap_sets, Rel.image, Filter.mem_sets, Set.mem_setOf_eq, Rel.core_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, Set.Subset.trans (Rel.core_mono _ hv) h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨Rel.core s t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩
@[simp]
theorem rcomap_compose (r : Rel α β) (s : Rel β γ) : rcomap r ∘ rcomap s = rcomap (r.comp s) :=
  funext <| rcomap_rcomap _ _
theorem rtendsto_iff_le_rcomap (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ l₁ ≤ l₂.rcomap r := by
  rw [rtendsto_def]
  simp_rw [← l₂.mem_sets]
  constructor
  · simpa [Filter.le_def, rcomap, Rel.mem_image] using fun h s t tl₂ => mem_of_superset (h t tl₂)
  · simpa [Filter.le_def, rcomap, Rel.mem_image] using fun h t tl₂ => h _ t tl₂ Set.Subset.rfl
def rcomap' (r : Rel α β) (f : Filter β) : Filter α where
  sets := Rel.image (fun s t => r.preimage s ⊆ t) f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁,
      (@Rel.preimage_inter _ _ r _ _).trans (Set.inter_subset_inter ha₂ hb₂)⟩
@[simp]
theorem mem_rcomap' (r : Rel α β) (l : Filter β) (s : Set α) :
    s ∈ l.rcomap' r ↔ ∃ t ∈ l, r.preimage t ⊆ s :=
  Iff.rfl
theorem rcomap'_sets (r : Rel α β) (f : Filter β) :
    (rcomap' r f).sets = Rel.image (fun s t => r.preimage s ⊆ t) f.sets :=
  rfl
@[simp]
theorem rcomap'_rcomap' (r : Rel α β) (s : Rel β γ) (l : Filter γ) :
    rcomap' r (rcomap' s l) = rcomap' (r.comp s) l :=
  Filter.ext fun t => by
    simp only [mem_rcomap', Rel.preimage_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, (Rel.preimage_mono _ hv).trans h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨s.preimage t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩
@[simp]
theorem rcomap'_compose (r : Rel α β) (s : Rel β γ) : rcomap' r ∘ rcomap' s = rcomap' (r.comp s) :=
  funext <| rcomap'_rcomap' _ _
def RTendsto' (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' r
theorem rtendsto'_def (r : Rel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s ∈ l₁ := by
  unfold RTendsto' rcomap'; constructor
  · simpa [le_def, Rel.mem_image] using fun h s hs => h _ _ hs Set.Subset.rfl
  · simpa [le_def, Rel.mem_image] using fun h s t ht => mem_of_superset (h t ht)
theorem tendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ RTendsto (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto_def, Rel.core, Set.preimage]
theorem tendsto_iff_rtendsto' (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ RTendsto' (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto'_def, Rel.preimage_def, Set.preimage]
def pmap (f : α →. β) (l : Filter α) : Filter β :=
  Filter.rmap f.graph' l
@[simp]
theorem mem_pmap (f : α →. β) (l : Filter α) (s : Set β) : s ∈ l.pmap f ↔ f.core s ∈ l :=
  Iff.rfl
def PTendsto (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.pmap f ≤ l₂
theorem ptendsto_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f.core s ∈ l₁ :=
  Iff.rfl
theorem ptendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α →. β) :
    PTendsto f l₁ l₂ ↔ RTendsto f.graph' l₁ l₂ :=
  Iff.rfl
theorem pmap_res (l : Filter α) (s : Set α) (f : α → β) :
    pmap (PFun.res f s) l = map f (l ⊓ 𝓟 s) := by
  ext t
  simp only [PFun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or]
  rfl
theorem tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : Filter β) (s : Set α) (f : α → β) :
    Tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ PTendsto (PFun.res f s) l₁ l₂ := by
  simp only [Tendsto, PTendsto, pmap_res]
theorem tendsto_iff_ptendsto_univ (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ PTendsto (PFun.res f Set.univ) l₁ l₂ := by
  rw [← tendsto_iff_ptendsto]
  simp [principal_univ]
def pcomap' (f : α →. β) (l : Filter β) : Filter α :=
  Filter.rcomap' f.graph' l
def PTendsto' (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' f.graph'
theorem ptendsto'_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁ :=
  rtendsto'_def _ _ _
theorem ptendsto_of_ptendsto' {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} :
    PTendsto' f l₁ l₂ → PTendsto f l₁ l₂ := by
  rw [ptendsto_def, ptendsto'_def]
  exact fun h s sl₂ => mem_of_superset (h s sl₂) (PFun.preimage_subset_core _ _)
theorem ptendsto'_of_ptendsto {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} (h : f.Dom ∈ l₁) :
    PTendsto f l₁ l₂ → PTendsto' f l₁ l₂ := by
  rw [ptendsto_def, ptendsto'_def]
  intro h' s sl₂
  rw [PFun.preimage_eq]
  exact inter_mem (h' s sl₂) h
end Filter