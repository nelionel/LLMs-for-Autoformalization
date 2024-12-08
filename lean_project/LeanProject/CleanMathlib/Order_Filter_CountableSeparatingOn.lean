import Mathlib.Order.Filter.CountableInter
open Function Set Filter
class HasCountableSeparatingOn (α : Type*) (p : Set α → Prop) (t : Set α) : Prop where
  exists_countable_separating : ∃ S : Set (Set α), S.Countable ∧ (∀ s ∈ S, p s) ∧
    ∀ x ∈ t, ∀ y ∈ t, (∀ s ∈ S, x ∈ s ↔ y ∈ s) → x = y
theorem exists_countable_separating (α : Type*) (p : Set α → Prop) (t : Set α)
    [h : HasCountableSeparatingOn α p t] :
    ∃ S : Set (Set α), S.Countable ∧ (∀ s ∈ S, p s) ∧
      ∀ x ∈ t, ∀ y ∈ t, (∀ s ∈ S, x ∈ s ↔ y ∈ s) → x = y :=
  h.1
theorem exists_nonempty_countable_separating (α : Type*) {p : Set α → Prop} {s₀} (hp : p s₀)
    (t : Set α) [HasCountableSeparatingOn α p t] :
    ∃ S : Set (Set α), S.Nonempty ∧ S.Countable ∧ (∀ s ∈ S, p s) ∧
      ∀ x ∈ t, ∀ y ∈ t, (∀ s ∈ S, x ∈ s ↔ y ∈ s) → x = y :=
  let ⟨S, hSc, hSp, hSt⟩ := exists_countable_separating α p t
  ⟨insert s₀ S, insert_nonempty _ _, hSc.insert _, forall_insert_of_forall hSp hp,
    fun x hx y hy hxy ↦ hSt x hx y hy <| forall_of_forall_insert hxy⟩
theorem exists_seq_separating (α : Type*) {p : Set α → Prop} {s₀} (hp : p s₀) (t : Set α)
    [HasCountableSeparatingOn α p t] :
    ∃ S : ℕ → Set α, (∀ n, p (S n)) ∧ ∀ x ∈ t, ∀ y ∈ t, (∀ n, x ∈ S n ↔ y ∈ S n) → x = y := by
  rcases exists_nonempty_countable_separating α hp t with ⟨S, hSne, hSc, hS⟩
  rcases hSc.exists_eq_range hSne with ⟨S, rfl⟩
  use S
  simpa only [forall_mem_range] using hS
theorem HasCountableSeparatingOn.mono {α} {p₁ p₂ : Set α → Prop} {t₁ t₂ : Set α}
    [h : HasCountableSeparatingOn α p₁ t₁] (hp : ∀ s, p₁ s → p₂ s) (ht : t₂ ⊆ t₁) :
    HasCountableSeparatingOn α p₂ t₂ where
  exists_countable_separating :=
    let ⟨S, hSc, hSp, hSt⟩ := h.1
    ⟨S, hSc, fun s hs ↦ hp s (hSp s hs), fun x hx y hy ↦ hSt x (ht hx) y (ht hy)⟩
theorem HasCountableSeparatingOn.of_subtype {α : Type*} {p : Set α → Prop} {t : Set α}
    {q : Set t → Prop} [h : HasCountableSeparatingOn t q univ]
    (hpq : ∀ U, q U → ∃ V, p V ∧ (↑) ⁻¹' V = U) : HasCountableSeparatingOn α p t := by
  rcases h.1 with ⟨S, hSc, hSq, hS⟩
  choose! V hpV hV using fun s hs ↦ hpq s (hSq s hs)
  refine ⟨⟨V '' S, hSc.image _, forall_mem_image.2 hpV, fun x hx y hy h ↦ ?_⟩⟩
  refine congr_arg Subtype.val (hS ⟨x, hx⟩ trivial ⟨y, hy⟩ trivial fun U hU ↦ ?_)
  rw [← hV U hU]
  exact h _ (mem_image_of_mem _ hU)
theorem HasCountableSeparatingOn.subtype_iff {α : Type*} {p : Set α → Prop} {t : Set α} :
    HasCountableSeparatingOn t (fun u ↦ ∃ v, p v ∧ (↑) ⁻¹' v = u) univ ↔
    HasCountableSeparatingOn α p t := by
  constructor <;> intro h
  · exact h.of_subtype <| fun s ↦ id
  rcases h with ⟨S, Sct, Sp, hS⟩
  use {Subtype.val ⁻¹' s | s ∈ S}, Sct.image _, ?_, ?_
  · rintro u ⟨t, tS, rfl⟩
    exact ⟨t, Sp _ tS, rfl⟩
  rintro x - y - hxy
  exact Subtype.val_injective <| hS _ (Subtype.coe_prop _) _ (Subtype.coe_prop _)
    fun s hs ↦ hxy (Subtype.val ⁻¹' s) ⟨s, hs, rfl⟩
namespace Filter
variable {α β : Type*} {l : Filter α} [CountableInterFilter l] {f g : α → β}
theorem exists_subset_subsingleton_mem_of_forall_separating (p : Set α → Prop)
    {s : Set α} [h : HasCountableSeparatingOn α p s] (hs : s ∈ l)
    (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) : ∃ t, t ⊆ s ∧ t.Subsingleton ∧ t ∈ l := by
  rcases h.1 with ⟨S, hSc, hSp, hS⟩
  refine ⟨s ∩ ⋂₀ (S ∩ l.sets) ∩ ⋂ (U ∈ S) (_ : Uᶜ ∈ l), Uᶜ, ?_, ?_, ?_⟩
  · exact fun _ h ↦ h.1.1
  · intro x hx y hy
    simp only [mem_sInter, mem_inter_iff, mem_iInter, mem_compl_iff] at hx hy
    refine hS x hx.1.1 y hy.1.1 (fun s hsS ↦ ?_)
    cases hl s (hSp s hsS) with
    | inl hsl => simp only [hx.1.2 s ⟨hsS, hsl⟩, hy.1.2 s ⟨hsS, hsl⟩]
    | inr hsl => simp only [hx.2 s hsS hsl, hy.2 s hsS hsl]
  · exact inter_mem
      (inter_mem hs ((countable_sInter_mem (hSc.mono inter_subset_left)).2 fun _ h ↦ h.2))
      ((countable_bInter_mem hSc).2 fun U hU ↦ iInter_mem'.2 id)
theorem exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (p : Set α → Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s ∈ l) (hne : s.Nonempty)
    (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) : ∃ a ∈ s, {a} ∈ l := by
  rcases exists_subset_subsingleton_mem_of_forall_separating p hs hl with ⟨t, hts, ht, htl⟩
  rcases ht.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact hne.imp fun a ha ↦ ⟨ha, mem_of_superset htl (empty_subset _)⟩
  · exact ⟨x, hts rfl, htl⟩
theorem exists_singleton_mem_of_mem_of_forall_separating [Nonempty α] (p : Set α → Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s ∈ l) (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ a, {a} ∈ l := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ‹Nonempty α›.elim fun a ↦ ⟨a, mem_of_superset hs (empty_subset _)⟩
  · exact (exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p hs hne hl).imp fun _ ↦
      And.right
theorem exists_subsingleton_mem_of_forall_separating (p : Set α → Prop)
    [HasCountableSeparatingOn α p univ] (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ s : Set α, s.Subsingleton ∧ s ∈ l :=
  let ⟨t, _, hts, htl⟩ := exists_subset_subsingleton_mem_of_forall_separating p univ_mem hl
  ⟨t, hts, htl⟩
theorem exists_singleton_mem_of_forall_separating [Nonempty α] (p : Set α → Prop)
    [HasCountableSeparatingOn α p univ] (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ x : α, {x} ∈ l :=
  exists_singleton_mem_of_mem_of_forall_separating p univ_mem hl
theorem exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating (p : Set β → Prop)
    {s : Set β} [HasCountableSeparatingOn β p s] (hs : ∀ᶠ x in l, f x ∈ s) (hne : s.Nonempty)
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a ∈ s, f =ᶠ[l] const α a :=
  exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p (l := map f l) hs hne h
theorem exists_eventuallyEq_const_of_eventually_mem_of_forall_separating [Nonempty β]
    (p : Set β → Prop) {s : Set β} [HasCountableSeparatingOn β p s] (hs : ∀ᶠ x in l, f x ∈ s)
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_mem_of_forall_separating (l := map f l) p hs h
theorem exists_eventuallyEq_const_of_forall_separating [Nonempty β] (p : Set β → Prop)
    [HasCountableSeparatingOn β p univ]
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_forall_separating (l := map f l) p h
namespace EventuallyEq
theorem of_eventually_mem_of_forall_separating_mem_iff (p : Set β → Prop) {s : Set β}
    [h' : HasCountableSeparatingOn β p s] (hf : ∀ᶠ x in l, f x ∈ s) (hg : ∀ᶠ x in l, g x ∈ s)
    (h : ∀ U : Set β, p U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) : f =ᶠ[l] g := by
  rcases h'.1 with ⟨S, hSc, hSp, hS⟩
  have H : ∀ᶠ x in l, ∀ s ∈ S, f x ∈ s ↔ g x ∈ s :=
    (eventually_countable_ball hSc).2 fun s hs ↦ (h _ (hSp _ hs))
  filter_upwards [H, hf, hg] with x hx hxf hxg using hS _ hxf _ hxg hx
theorem of_forall_separating_mem_iff (p : Set β → Prop)
    [HasCountableSeparatingOn β p univ] (h : ∀ U : Set β, p U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) :
    f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p (s := univ) univ_mem univ_mem h
theorem of_eventually_mem_of_forall_separating_preimage (p : Set β → Prop) {s : Set β}
    [HasCountableSeparatingOn β p s] (hf : ∀ᶠ x in l, f x ∈ s) (hg : ∀ᶠ x in l, g x ∈ s)
    (h : ∀ U : Set β, p U → f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p hf hg fun U hU ↦ (h U hU).mem_iff
theorem of_forall_separating_preimage (p : Set β → Prop) [HasCountableSeparatingOn β p univ]
    (h : ∀ U : Set β, p U → f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_preimage p (s := univ) univ_mem univ_mem h
end EventuallyEq
end Filter