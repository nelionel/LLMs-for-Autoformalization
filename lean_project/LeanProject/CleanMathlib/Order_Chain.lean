import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
open Set
variable {α β : Type*}
section Chain
variable (r : α → α → Prop)
local infixl:50 " ≺ " => r
def IsChain (s : Set α) : Prop :=
  s.Pairwise fun x y => x ≺ y ∨ y ≺ x
def SuperChain (s t : Set α) : Prop :=
  IsChain r t ∧ s ⊂ t
def IsMaxChain (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t
variable {r} {c c₁ c₂ s t : Set α} {a b x y : α}
@[simp] lemma IsChain.empty : IsChain r ∅ := pairwise_empty _
@[simp] lemma IsChain.singleton : IsChain r {a} := pairwise_singleton ..
@[deprecated (since := "2024-11-25")] alias isChain_empty := IsChain.empty
theorem Set.Subsingleton.isChain (hs : s.Subsingleton) : IsChain r s :=
  hs.pairwise _
theorem IsChain.mono : s ⊆ t → IsChain r t → IsChain r s :=
  Set.Pairwise.mono
theorem IsChain.mono_rel {r' : α → α → Prop} (h : IsChain r s) (h_imp : ∀ x y, r x y → r' x y) :
    IsChain r' s :=
  h.mono' fun x y => Or.imp (h_imp x y) (h_imp y x)
theorem IsChain.symm (h : IsChain r s) : IsChain (flip r) s :=
  h.mono' fun _ _ => Or.symm
theorem isChain_of_trichotomous [IsTrichotomous α r] (s : Set α) : IsChain r s :=
  fun a _ b _ hab => (trichotomous_of r a b).imp_right fun h => h.resolve_left hab
protected theorem IsChain.insert (hs : IsChain r s) (ha : ∀ b ∈ s, a ≠ b → a ≺ b ∨ b ≺ a) :
    IsChain r (insert a s) :=
  hs.insert_of_symmetric (fun _ _ => Or.symm) ha
lemma IsChain.pair (h : r a b) : IsChain r {a, b} :=
  IsChain.singleton.insert fun _ hb _ ↦ .inl <| (eq_of_mem_singleton hb).symm.recOn ‹_›
theorem isChain_univ_iff : IsChain r (univ : Set α) ↔ IsTrichotomous α r := by
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun h => @isChain_of_trichotomous _ _ h univ⟩
  rw [or_left_comm, or_iff_not_imp_left]
  exact h trivial trivial
theorem IsChain.image (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
    (h : ∀ x y, r x y → s (f x) (f y)) {c : Set α} (hrc : IsChain r c) : IsChain s (f '' c) :=
  fun _ ⟨_, ha₁, ha₂⟩ _ ⟨_, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).imp (h _ _) (h _ _)
theorem Monotone.isChain_range [LinearOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    IsChain (· ≤ ·) (range f) := by
  rw [← image_univ]
  exact (isChain_of_trichotomous _).image (· ≤ ·) _ _ hf
theorem IsChain.lt_of_le [PartialOrder α] {s : Set α} (h : IsChain (· ≤ ·) s) :
    IsChain (· < ·) s := fun _a ha _b hb hne ↦
  (h ha hb hne).imp hne.lt_of_le hne.lt_of_le'
section Total
variable [IsRefl α r]
theorem IsChain.total (h : IsChain r s) (hx : x ∈ s) (hy : y ∈ s) : x ≺ y ∨ y ≺ x :=
  (eq_or_ne x y).elim (fun e => Or.inl <| e ▸ refl _) (h hx hy)
theorem IsChain.directedOn (H : IsChain r s) : DirectedOn r s := fun x hx y hy =>
  ((H.total hx hy).elim fun h => ⟨y, hy, h, refl _⟩) fun h => ⟨x, hx, refl _, h⟩
protected theorem IsChain.directed {f : β → α} {c : Set β} (h : IsChain (f ⁻¹'o r) c) :
    Directed r fun x : { a : β // a ∈ c } => f x :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    (by_cases fun hab : a = b => by
      simp only [hab, exists_prop, and_self_iff, Subtype.exists]
      exact ⟨b, hb, refl _⟩)
    fun hab => ((h ha hb hab).elim fun h => ⟨⟨b, hb⟩, h, refl _⟩) fun h => ⟨⟨a, ha⟩, refl _, h⟩
theorem IsChain.exists3 (hchain : IsChain r s) [IsTrans α r] {a b c} (mem1 : a ∈ s) (mem2 : b ∈ s)
    (mem3 : c ∈ s) : ∃ (z : _) (_ : z ∈ s), r a z ∧ r b z ∧ r c z := by
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) a mem1 b mem2 with ⟨z, mem4, H1, H2⟩
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) z mem4 c mem3 with
    ⟨z', mem5, H3, H4⟩
  exact ⟨z', mem5, _root_.trans H1 H3, _root_.trans H2 H3, H4⟩
end Total
theorem IsMaxChain.isChain (h : IsMaxChain r s) : IsChain r s :=
  h.1
theorem IsMaxChain.not_superChain (h : IsMaxChain r s) : ¬SuperChain r s t := fun ht =>
  ht.2.ne <| h.2 ht.1 ht.2.1
theorem IsMaxChain.bot_mem [LE α] [OrderBot α] (h : IsMaxChain (· ≤ ·) s) : ⊥ ∈ s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inl bot_le) <| subset_insert _ _).symm ▸ mem_insert _ _
theorem IsMaxChain.top_mem [LE α] [OrderTop α] (h : IsMaxChain (· ≤ ·) s) : ⊤ ∈ s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inr le_top) <| subset_insert _ _).symm ▸ mem_insert _ _
lemma IsMaxChain.image {s : β → β → Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxChain r c) :
    IsMaxChain s (e '' c) where
  left := hc.isChain.image _ _ _ fun _ _ ↦ by exact e.map_rel_iff.2
  right t ht hf := by
    rw [← e.coe_fn_toEquiv, ← e.toEquiv.eq_preimage_iff_image_eq, preimage_equiv_eq_image_symm]
    exact hc.2 (ht.image _ _ _ fun _ _ ↦ by exact e.symm.map_rel_iff.2)
      ((e.toEquiv.subset_symm_image _ _).2 hf)
open Classical in
def SuccChain (r : α → α → Prop) (s : Set α) : Set α :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then h.choose else s
theorem succChain_spec (h : ∃ t, IsChain r s ∧ SuperChain r s t) :
    SuperChain r s (SuccChain r s) := by
  have : IsChain r s ∧ SuperChain r s h.choose := h.choose_spec
  simpa [SuccChain, dif_pos, exists_and_left.mp h] using this.2
open Classical in
theorem IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s) :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then (succChain_spec h).1
  else by
    rw [exists_and_left] at h
    simpa [SuccChain, dif_neg, h] using hs
theorem IsChain.superChain_succChain (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s) :
    SuperChain r s (SuccChain r s) := by
  simp only [IsMaxChain, _root_.not_and, not_forall, exists_prop, exists_and_left] at hs₂
  obtain ⟨t, ht, hst⟩ := hs₂ hs₁
  exact succChain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩
open Classical in
theorem subset_succChain : s ⊆ SuccChain r s :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then (succChain_spec h).2.1
  else by
    rw [exists_and_left] at h
    simp [SuccChain, dif_neg, h, Subset.rfl]
inductive ChainClosure (r : α → α → Prop) : Set α → Prop
  | succ : ∀ {s}, ChainClosure r s → ChainClosure r (SuccChain r s)
  | union : ∀ {s}, (∀ a ∈ s, ChainClosure r a) → ChainClosure r (⋃₀s)
def maxChain (r : α → α → Prop) : Set α :=
  ⋃₀ setOf (ChainClosure r)
theorem chainClosure_empty : ChainClosure r ∅ := by
  have : ChainClosure r (⋃₀∅) := ChainClosure.union fun a h => (not_mem_empty _ h).elim
  simpa using this
theorem chainClosure_maxChain : ChainClosure r (maxChain r) :=
  ChainClosure.union fun _ => id
private theorem chainClosure_succ_total_aux (hc₁ : ChainClosure r c₁)
    (h : ∀ ⦃c₃⦄, ChainClosure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ SuccChain r c₃ ⊆ c₂) :
    SuccChain r c₂ ⊆ c₁ ∨ c₁ ⊆ c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    cases' ih with ih ih
    · exact Or.inl (ih.trans subset_succChain)
    · exact (h hc₃ ih).imp_left fun (h : c₂ = c₃) => h ▸ Subset.rfl
  | union _ ih =>
    refine or_iff_not_imp_left.2 fun hn => sUnion_subset fun a ha => ?_
    exact (ih a ha).resolve_left fun h => hn <| h.trans <| subset_sUnion_of_mem ha
private theorem chainClosure_succ_total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (h : c₁ ⊆ c₂) : c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂ := by
  induction hc₂ generalizing c₁ hc₁ with
  | succ _ ih =>
    refine ((chainClosure_succ_total_aux hc₁) fun c₁ => ih).imp h.antisymm' fun h₁ => ?_
    obtain rfl | h₂ := ih hc₁ h₁
    · exact Subset.rfl
    · exact h₂.trans subset_succChain
  | union _ ih =>
    apply Or.imp_left h.antisymm'
    apply by_contradiction
    simp only [sUnion_subset_iff, not_or, not_forall, exists_prop, and_imp, forall_exists_index]
    intro c₃ hc₃ h₁ h₂
    obtain h | h := chainClosure_succ_total_aux hc₁ fun c₄ => ih _ hc₃
    · exact h₁ (subset_succChain.trans h)
    obtain h' | h' := ih c₃ hc₃ hc₁ h
    · exact h₁ h'.subset
    · exact h₂ (h'.trans <| subset_sUnion_of_mem hc₃)
theorem ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) :
    c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
  ((chainClosure_succ_total_aux hc₂) fun _ hc₃ => chainClosure_succ_total hc₃ hc₁).imp_left
    subset_succChain.trans
theorem ChainClosure.succ_fixpoint (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (hc : SuccChain r c₂ = c₂) : c₁ ⊆ c₂ := by
  induction hc₁ with
  | succ hc₁ h => exact (chainClosure_succ_total hc₁ hc₂ h).elim (fun h => h ▸ hc.subset) id
  | union _ ih => exact sUnion_subset ih
theorem ChainClosure.succ_fixpoint_iff (hc : ChainClosure r c) :
    SuccChain r c = c ↔ c = maxChain r :=
  ⟨fun h => (subset_sUnion_of_mem hc).antisymm <| chainClosure_maxChain.succ_fixpoint hc h,
    fun h => subset_succChain.antisymm' <| (subset_sUnion_of_mem hc.succ).trans h.symm.subset⟩
theorem ChainClosure.isChain (hc : ChainClosure r c) : IsChain r c := by
  induction hc with
  | succ _ h => exact h.succ
  | union hs h =>
    exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq =>
      ((hs _ ht₁).total <| hs _ ht₂).elim (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht =>
        h t₁ ht₁ hc₁ (ht hc₂) hneq
theorem maxChain_spec : IsMaxChain r (maxChain r) :=
  by_contradiction fun h =>
    let ⟨_, H⟩ := chainClosure_maxChain.isChain.superChain_succChain h
    H.ne (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm
end Chain
structure Flag (α : Type*) [LE α] where
  carrier : Set α
  Chain' : IsChain (· ≤ ·) carrier
  max_chain' : ∀ ⦃s⦄, IsChain (· ≤ ·) s → carrier ⊆ s → carrier = s
namespace Flag
section LE
variable [LE α] {s t : Flag α} {a : α}
instance : SetLike (Flag α) α where
  coe := carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr
@[ext]
theorem ext : (s : Set α) = t → s = t :=
  SetLike.ext'
theorem mem_coe_iff : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl
@[simp]
theorem coe_mk (s : Set α) (h₁ h₂) : (mk s h₁ h₂ : Set α) = s :=
  rfl
@[simp]
theorem mk_coe (s : Flag α) : mk (s : Set α) s.Chain' s.max_chain' = s :=
  ext rfl
theorem chain_le (s : Flag α) : IsChain (· ≤ ·) (s : Set α) :=
  s.Chain'
protected theorem maxChain (s : Flag α) : IsMaxChain (· ≤ ·) (s : Set α) :=
  ⟨s.chain_le, s.max_chain'⟩
theorem top_mem [OrderTop α] (s : Flag α) : (⊤ : α) ∈ s :=
  s.maxChain.top_mem
theorem bot_mem [OrderBot α] (s : Flag α) : (⊥ : α) ∈ s :=
  s.maxChain.bot_mem
def ofIsMaxChain (c : Set α) (hc : IsMaxChain (· ≤ ·) c) : Flag α := ⟨c, hc.isChain, hc.2⟩
@[simp, norm_cast]
lemma coe_ofIsMaxChain (c : Set α) (hc) : ofIsMaxChain c hc = c := rfl
end LE
section Preorder
variable [Preorder α] [Preorder β] {a b : α} {s : Flag α}
protected theorem le_or_le (s : Flag α) (ha : a ∈ s) (hb : b ∈ s) : a ≤ b ∨ b ≤ a :=
  s.chain_le.total ha hb
instance [OrderTop α] (s : Flag α) : OrderTop s :=
  Subtype.orderTop s.top_mem
instance [OrderBot α] (s : Flag α) : OrderBot s :=
  Subtype.orderBot s.bot_mem
instance [BoundedOrder α] (s : Flag α) : BoundedOrder s :=
  Subtype.boundedOrder s.bot_mem s.top_mem
lemma mem_iff_forall_le_or_ge : a ∈ s ↔ ∀ ⦃b⦄, b ∈ s → a ≤ b ∨ b ≤ a :=
  ⟨fun ha b => s.le_or_le ha, fun hb =>
    of_not_not fun ha =>
      Set.ne_insert_of_not_mem _ ‹_› <|
        s.maxChain.2 (s.chain_le.insert fun c hc _ => hb hc) <| Set.subset_insert _ _⟩
def map (e : α ≃o β) : Flag α ≃ Flag β
    where
  toFun s := ofIsMaxChain _ (s.maxChain.image e)
  invFun s := ofIsMaxChain _ (s.maxChain.image e.symm)
  left_inv s := ext <| e.symm_image_image s
  right_inv s := ext <| e.image_symm_image s
@[simp, norm_cast] lemma coe_map (e : α ≃o β) (s : Flag α) : ↑(map e s) = e '' s := rfl
@[simp] lemma symm_map (e : α ≃o β) : (map e).symm = map e.symm := rfl
end Preorder
section PartialOrder
variable [PartialOrder α]
theorem chain_lt (s : Flag α) : IsChain (· < ·) (s : Set α) := s.chain_le.lt_of_le
instance [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] (s : Flag α) :
    LinearOrder s :=
  { Subtype.partialOrder _ with
    le_total := fun a b => s.le_or_le a.2 b.2
    decidableLE := Subtype.decidableLE
    decidableLT := Subtype.decidableLT }
end PartialOrder
instance [LinearOrder α] : Unique (Flag α) where
  default := ⟨univ, isChain_of_trichotomous _, fun s _ => s.subset_univ.antisymm'⟩
  uniq s := SetLike.coe_injective <| s.3 (isChain_of_trichotomous _) <| subset_univ _
end Flag