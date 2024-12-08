import Mathlib.Order.Chain
import Mathlib.Order.Minimal
open Set
variable {α β : Type*} {r : α → α → Prop} {c : Set α}
local infixl:50 " ≺ " => r
theorem exists_maximal_of_chains_bounded (h : ∀ c, IsChain r c → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  have : ∃ ub, ∀ a ∈ maxChain r, a ≺ ub := h _ <| maxChain_spec.left
  let ⟨ub, (hub : ∀ a ∈ maxChain r, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : IsChain r (insert a <| maxChain r) :=
      maxChain_spec.1.insert fun b hb _ => Or.inr <| trans (hub b hb) ha
    hub a <| by
      rw [maxChain_spec.right this (subset_insert _ _)]
      exact mem_insert _ _⟩
theorem exists_maximal_of_nonempty_chains_bounded [Nonempty α]
    (h : ∀ c, IsChain r c → c.Nonempty → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim
        (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x ∈ (∅ : Set α)).elim⟩) (h c hc))
    trans
section Preorder
variable [Preorder α]
theorem zorn_le (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) : ∃ m : α, IsMax m :=
  exists_maximal_of_chains_bounded h le_trans
theorem zorn_le_nonempty [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) : ∃ m : α, IsMax m :=
  exists_maximal_of_nonempty_chains_bounded h le_trans
theorem zorn_le₀ (s : Set α) (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
    ∃ m, Maximal (· ∈ s) m :=
  let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_le s _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨_, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq
            exact hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun ⟨_, _⟩ hc => hub _ ⟨_, hc, rfl⟩⟩
  ⟨m, hms, fun z hzs hmz => @h ⟨z, hzs⟩ hmz⟩
theorem zorn_le_nonempty₀ (s : Set α)
    (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α) (hxs : x ∈ s) :
    ∃ m, x ≤ m ∧ Maximal (· ∈ s) m := by
  have H := zorn_le₀ ({ y ∈ s | x ≤ y }) fun c hcs hc => ?_
  · rcases H with ⟨m, ⟨hms, hxm⟩, hm⟩
    exact ⟨m, hxm, hms, fun z hzs hmz => @hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  · rcases c.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    · exact ⟨x, ⟨hxs, le_rfl⟩, fun z => False.elim⟩
    · rcases ih c (fun z hz => (hcs hz).1) hc y hy with ⟨z, hzs, hz⟩
      exact ⟨z, ⟨hzs, (hcs hy).2.trans <| hz _ hy⟩, hz⟩
theorem zorn_le_nonempty_Ici₀ (a : α)
    (ih : ∀ c ⊆ Ici a, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub, ∀ z ∈ c, z ≤ ub) (x : α) (hax : a ≤ x) :
    ∃ m, x ≤ m ∧ IsMax m   := by
  let ⟨m, hxm, ham, hm⟩ := zorn_le_nonempty₀ (Ici a) (fun c hca hc y hy ↦ ?_) x hax
  · exact ⟨m, hxm, fun z hmz => hm (ham.trans hmz) hmz⟩
  · have ⟨ub, hub⟩ := ih c hca hc y hy
    exact ⟨ub, (hca hy).trans (hub y hy), hub⟩
end Preorder
theorem zorn_subset (S : Set (Set α))
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) : ∃ m, Maximal (· ∈ S) m :=
  zorn_le₀ S h
theorem zorn_subset_nonempty (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x) (hx : x ∈ S) :
    ∃ m, x ⊆ m ∧ Maximal (· ∈ S) m :=
  zorn_le_nonempty₀ _ (fun _ cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx
theorem zorn_superset (S : Set (Set α))
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) : ∃ m, Minimal (· ∈ S) m :=
  (@zorn_le₀ (Set α)ᵒᵈ _ S) fun c cS hc => h c cS hc.symm
theorem zorn_superset_nonempty (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) (x) (hx : x ∈ S) :
    ∃ m, m ⊆ x ∧ Minimal (· ∈ S) m :=
  @zorn_le_nonempty₀ (Set α)ᵒᵈ _ S (fun _ cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx
theorem IsChain.exists_maxChain (hc : IsChain r c) : ∃ M, @IsMaxChain _ r M ∧ c ⊆ M := by
  have H := zorn_subset_nonempty { s | c ⊆ s ∧ IsChain r s } ?_ c ⟨Subset.rfl, hc⟩
  · obtain ⟨M, hcM, hM⟩ := H
    exact ⟨M, ⟨hM.prop.2, fun d hd hMd ↦ hM.eq_of_subset ⟨hcM.trans hMd, hd⟩ hMd⟩, hcM⟩
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine
    ⟨⋃₀cs, ⟨fun _ ha => Set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, ?_⟩, fun _ =>
      Set.subset_sUnion_of_mem⟩
  rintro y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz
  obtain rfl | hsseq := eq_or_ne sy sz
  · exact (hcs₀ hsy).right hysy hzsz hyz
  cases' hcs₁ hsy hsz hsseq with h h
  · exact (hcs₀ hsz).right (h hysy) hzsz hyz
  · exact (hcs₀ hsy).right hysy (h hzsz) hyz