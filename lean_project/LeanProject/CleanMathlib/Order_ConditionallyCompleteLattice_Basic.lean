import Mathlib.Data.Set.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Defs
assert_not_exists Multiset
open Function OrderDual Set
variable {α β γ : Type*} {ι : Sort*}
section
variable [Preorder α]
open Classical in
noncomputable instance WithTop.instSupSet [SupSet α] :
    SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) ↦ (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩
open Classical in
noncomputable instance WithTop.instInfSet [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α))⟩
noncomputable instance WithBot.instSupSet [SupSet α] : SupSet (WithBot α) :=
  ⟨(WithTop.instInfSet (α := αᵒᵈ)).sInf⟩
noncomputable instance WithBot.instInfSet [InfSet α] :
    InfSet (WithBot α) :=
  ⟨(WithTop.instSupSet (α := αᵒᵈ)).sSup⟩
theorem WithTop.sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  (if_neg hs).trans <| if_pos hs'
theorem WithTop.sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) (h's : BddBelow s) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  if_neg <| by simp [hs, h's]
theorem WithBot.sInf_eq [InfSet α] {s : Set (WithBot α)} (hs : ⊥ ∉ s)
    (hs' : BddBelow ((↑) ⁻¹' s : Set α)) : sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  (if_neg hs).trans <| if_pos hs'
theorem WithBot.sSup_eq [SupSet α] {s : Set (WithBot α)} (hs : ¬s ⊆ {⊥}) (h's : BddAbove s) :
    sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  WithTop.sInf_eq (α := αᵒᵈ) hs h's
@[simp]
theorem WithTop.sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| by simp
theorem WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · rcases h with h1 | h2
    · cases h1 (mem_image_of_mem _ hx)
    · exact (h2 (Monotone.map_bddBelow coe_mono h's)).elim
  · rw [preimage_image_eq]
    exact Option.some_injective _
theorem WithTop.coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  change _ = ite _ _ _
  rw [if_neg, preimage_image_eq, if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩
@[simp]
theorem WithBot.sSup_empty [SupSet α] : sSup (∅ : Set (WithBot α)) = ⊥ :=
  WithTop.sInf_empty (α := αᵒᵈ)
@[deprecated (since := "2024-06-10")] alias WithBot.csSup_empty := WithBot.sSup_empty
@[norm_cast]
theorem WithBot.coe_sSup' [SupSet α] {s : Set α} (hs : s.Nonempty) (h's : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  WithTop.coe_sInf' (α := αᵒᵈ) hs h's
@[norm_cast]
theorem WithBot.coe_sInf' [InfSet α] {s : Set α} (hs : BddBelow s) :
    ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  WithTop.coe_sSup' (α := αᵒᵈ) hs
end
instance ConditionallyCompleteLinearOrder.toLinearOrder [ConditionallyCompleteLinearOrder α] :
    LinearOrder α :=
  { ‹ConditionallyCompleteLinearOrder α› with
    min_def := fun a b ↦ by
      by_cases hab : a = b
      · simp [hab]
      · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
        · simp [h₁]
        · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂]
    max_def := fun a b ↦ by
      by_cases hab : a = b
      · simp [hab]
      · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
        · simp [h₁]
        · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂] }
attribute [instance 100] ConditionallyCompleteLinearOrderBot.toOrderBot
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  { ‹CompleteLattice α› with
    le_csSup := by intros; apply le_sSup; assumption
    csSup_le := by intros; apply sSup_le; assumption
    csInf_le := by intros; apply sInf_le; assumption
    le_csInf := by intros; apply le_sInf; assumption }
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type*}
    [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, h with
    csSup_empty := sSup_empty
    csSup_of_not_bddAbove := fun s H ↦ (H (OrderTop.bddAbove s)).elim
    csInf_of_not_bddBelow := fun s H ↦ (H (OrderBot.bddBelow s)).elim }
namespace OrderDual
instance instConditionallyCompleteLattice (α : Type*) [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice αᵒᵈ :=
  { OrderDual.instInf α, OrderDual.instSup α, OrderDual.instLattice α with
    le_csSup := ConditionallyCompleteLattice.csInf_le (α := α)
    csSup_le := ConditionallyCompleteLattice.le_csInf (α := α)
    le_csInf := ConditionallyCompleteLattice.csSup_le (α := α)
    csInf_le := ConditionallyCompleteLattice.le_csSup (α := α) }
instance (α : Type*) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder αᵒᵈ :=
  { OrderDual.instConditionallyCompleteLattice α, OrderDual.instLinearOrder α with
    csSup_of_not_bddAbove := ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow (α := α)
    csInf_of_not_bddBelow := ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove (α := α) }
end OrderDual
section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}
theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
  ConditionallyCompleteLattice.le_csSup s a h₁ h₂
theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  ConditionallyCompleteLattice.csSup_le s a h₁ h₂
theorem csInf_le (h₁ : BddBelow s) (h₂ : a ∈ s) : sInf s ≤ a :=
  ConditionallyCompleteLattice.csInf_le s a h₁ h₂
theorem le_csInf (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ sInf s :=
  ConditionallyCompleteLattice.le_csInf s a h₁ h₂
theorem le_csSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_csSup hs hb)
theorem csInf_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (csInf_le hs hb) h
theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
  csSup_le hs fun _ ha => le_csSup ht (h ha)
theorem csInf_le_csInf (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : sInf t ≤ sInf s :=
  le_csInf hs fun _ ha => csInf_le ht (h ha)
theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩
theorem csInf_le_iff (h : BddBelow s) (hs : s.Nonempty) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_csInf hs hb) h, fun hb => hb _ fun _ => csInf_le h⟩
theorem isLUB_csSup (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (sSup s) :=
  ⟨fun _ => le_csSup H, fun _ => csSup_le ne⟩
theorem isGLB_csInf (ne : s.Nonempty) (H : BddBelow s) : IsGLB s (sInf s) :=
  ⟨fun _ => csInf_le H, fun _ => le_csInf ne⟩
theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
  (isLUB_csSup ne ⟨a, H.1⟩).unique H
theorem IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a :=
  H.isLUB.csSup_eq H.nonempty
theorem IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s ∈ s :=
  H.csSup_eq.symm ▸ H.1
theorem IsGLB.csInf_eq (H : IsGLB s a) (ne : s.Nonempty) : sInf s = a :=
  (isGLB_csInf ne ⟨a, H.1⟩).unique H
theorem IsLeast.csInf_eq (H : IsLeast s a) : sInf s = a :=
  H.isGLB.csInf_eq H.nonempty
theorem IsLeast.csInf_mem (H : IsLeast s a) : sInf s ∈ s :=
  H.csInf_eq.symm ▸ H.1
theorem subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩
theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)
theorem le_csInf_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_csInf hs hb)
theorem csSup_lowerBounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    sSup (lowerBounds s) = sInf s :=
  (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB
theorem csInf_upperBounds_eq_csSup {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    sInf (upperBounds s) = sSup s :=
  (isGLB_csInf h <| hs.mono fun _ hx _ hy => hy hx).unique (isLUB_csSup hs h).isGLB
@[deprecated (since := "2024-08-25")]
alias csSup_lower_bounds_eq_csInf := csSup_lowerBounds_eq_csInf
@[deprecated (since := "2024-08-25")]
alias csInf_upper_bounds_eq_csSup := csInf_upperBounds_eq_csSup
theorem csSup_lowerBounds_range [Nonempty β] {f : β → α} (hf : BddBelow (range f)) :
    sSup (lowerBounds (range f)) = ⨅ i, f i :=
  csSup_lowerBounds_eq_csInf hf <| range_nonempty _
theorem csInf_upperBounds_range [Nonempty β] {f : β → α} (hf : BddAbove (range f)) :
    sInf (upperBounds (range f)) = ⨆ i, f i :=
  csInf_upperBounds_eq_csSup hf <| range_nonempty _
theorem not_mem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))
theorem not_mem_of_csSup_lt {x : α} {s : Set α} (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
  not_mem_of_lt_csInf (α := αᵒᵈ) h hs
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csSup ⟨b, H⟩ ha
theorem csInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ)
theorem lt_csSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)
theorem csInf_lt_of_lt : BddBelow s → a ∈ s → a < b → sInf s < b :=
  lt_csSup_of_lt (α := αᵒᵈ)
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨sInf t, fun x hx => le_csInf tne <| hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩
@[simp]
theorem csSup_singleton (a : α) : sSup {a} = a :=
  isGreatest_singleton.csSup_eq
@[simp]
theorem csInf_singleton (a : α) : sInf {a} = a :=
  isLeast_singleton.csInf_eq
@[simp]
theorem csSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)
@[simp]
theorem csInf_pair (a b : α) : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).csInf_eq (insert_nonempty _ _)
theorem csInf_le_csSup (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne
theorem csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl
theorem csInf_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    sInf (s ∪ t) = sInf s ⊓ sInf t :=
  csSup_union (α := αᵒᵈ) hs sne ht tne
theorem csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)
theorem le_csInf_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  csSup_inter_le (α := αᵒᵈ)
theorem csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)
theorem csInf_insert (hs : BddBelow s) (sne : s.Nonempty) : sInf (insert a s) = a ⊓ sInf s :=
  csSup_insert (α := αᵒᵈ) hs sne
@[simp]
theorem csInf_Icc (h : a ≤ b) : sInf (Icc a b) = a :=
  (isGLB_Icc h).csInf_eq (nonempty_Icc.2 h)
@[simp]
theorem csInf_Ici : sInf (Ici a) = a :=
  isLeast_Ici.csInf_eq
@[simp]
theorem csInf_Ico (h : a < b) : sInf (Ico a b) = a :=
  (isGLB_Ico h).csInf_eq (nonempty_Ico.2 h)
@[simp]
theorem csInf_Ioc [DenselyOrdered α] (h : a < b) : sInf (Ioc a b) = a :=
  (isGLB_Ioc h).csInf_eq (nonempty_Ioc.2 h)
@[simp]
theorem csInf_Ioi [NoMaxOrder α] [DenselyOrdered α] : sInf (Ioi a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw
@[simp]
theorem csInf_Ioo [DenselyOrdered α] (h : a < b) : sInf (Ioo a b) = a :=
  (isGLB_Ioo h).csInf_eq (nonempty_Ioo.2 h)
@[simp]
theorem csSup_Icc (h : a ≤ b) : sSup (Icc a b) = b :=
  (isLUB_Icc h).csSup_eq (nonempty_Icc.2 h)
@[simp]
theorem csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b :=
  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)
@[simp]
theorem csSup_Iic : sSup (Iic a) = a :=
  isGreatest_Iic.csSup_eq
@[simp]
theorem csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw
@[simp]
theorem csSup_Ioc (h : a < b) : sSup (Ioc a b) = b :=
  (isLUB_Ioc h).csSup_eq (nonempty_Ioc.2 h)
@[simp]
theorem csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b :=
  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : sSup s = b :=
  (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)
lemma sup_eq_top_of_top_mem [OrderTop α] (h : ⊤ ∈ s) : sSup s = ⊤ :=
  top_unique <| le_csSup (OrderTop.bddAbove s) h
lemma inf_eq_bot_of_bot_mem [OrderBot α] (h : ⊥ ∈ s) : sInf s = ⊥ :=
  bot_unique <| csInf_le (OrderBot.bddBelow s) h
end ConditionallyCompleteLattice
instance Pi.conditionallyCompleteLattice {ι : Type*} {α : ι → Type*}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.instLattice, Pi.supSet, Pi.infSet with
    le_csSup := fun _ f ⟨g, hg⟩ hf i =>
      le_csSup ⟨g i, Set.forall_mem_range.2 fun ⟨_, hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    csSup_le := fun s _ hs hf i =>
      (csSup_le (by haveI := hs.to_subtype; apply range_nonempty)) fun _ ⟨⟨_, hg⟩, hb⟩ =>
        hb ▸ hf hg i
    csInf_le := fun _ f ⟨g, hg⟩ hf i =>
      csInf_le ⟨g i, Set.forall_mem_range.2 fun ⟨_, hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    le_csInf := fun s _ hs hf i =>
      (le_csInf (by haveI := hs.to_subtype; apply range_nonempty)) fun _ ⟨⟨_, hg⟩, hb⟩ =>
        hb ▸ hf hg i }
section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] {s : Set α} {a b : α}
theorem exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  exact csSup_le hs hb
theorem exists_lt_of_csInf_lt (hs : s.Nonempty) (hb : sInf s < b) : ∃ a ∈ s, a < b :=
  exists_lt_of_lt_csSup (α := αᵒᵈ) hs hb
theorem lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSup s ↔ ∃ b ∈ s, a < b := by
  simpa only [not_le, not_forall₂, exists_prop] using (csSup_le_iff hb hs (a := a)).not
theorem csInf_lt_iff (hb : BddBelow s) (hs : s.Nonempty) : sInf s < a ↔ ∃ b ∈ s, b < a := by
  simpa only [not_le, not_forall₂, exists_prop] using (le_csInf_iff hb hs).not
theorem csSup_of_not_bddAbove {s : Set α} (hs : ¬BddAbove s) : sSup s = sSup ∅ :=
  ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove s hs
theorem csSup_eq_univ_of_not_bddAbove {s : Set α} (hs : ¬BddAbove s) : sSup s = sSup univ := by
  rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := univ)]
  contrapose! hs
  exact hs.mono (subset_univ _)
theorem csInf_of_not_bddBelow {s : Set α} (hs : ¬BddBelow s) : sInf s = sInf ∅ :=
  ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow s hs
theorem csInf_eq_univ_of_not_bddBelow {s : Set α} (hs : ¬BddBelow s) : sInf s = sInf univ :=
  csSup_eq_univ_of_not_bddAbove (α := αᵒᵈ) hs
theorem csSup_eq_csSup_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) (ht : ∀ y ∈ t, ∃ x ∈ s, y ≤ x) :
    sSup s = sSup t := by
  rcases eq_empty_or_nonempty s with rfl|s_ne
  · have : t = ∅ := eq_empty_of_forall_not_mem (fun y yt ↦ by simpa using ht y yt)
    rw [this]
  rcases eq_empty_or_nonempty t with rfl|t_ne
  · have : s = ∅ := eq_empty_of_forall_not_mem (fun x xs ↦ by simpa using hs x xs)
    rw [this]
  by_cases B : BddAbove s ∨ BddAbove t
  · have Bs : BddAbove s := by
      rcases B with hB|⟨b, hb⟩
      · exact hB
      · refine ⟨b, fun x hx ↦ ?_⟩
        rcases hs x hx with ⟨y, hy, hxy⟩
        exact hxy.trans (hb hy)
    have Bt : BddAbove t := by
      rcases B with ⟨b, hb⟩|hB
      · refine ⟨b, fun y hy ↦ ?_⟩
        rcases ht y hy with ⟨x, hx, hyx⟩
        exact hyx.trans (hb hx)
      · exact hB
    apply le_antisymm
    · apply csSup_le s_ne (fun x hx ↦ ?_)
      rcases hs x hx with ⟨y, yt, hxy⟩
      exact hxy.trans (le_csSup Bt yt)
    · apply csSup_le t_ne (fun y hy ↦ ?_)
      rcases ht y hy with ⟨x, xs, hyx⟩
      exact hyx.trans (le_csSup Bs xs)
  · simp [csSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]
theorem csInf_eq_csInf_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) (ht : ∀ y ∈ t, ∃ x ∈ s, x ≤ y) :
    sInf s = sInf t :=
  csSup_eq_csSup_of_forall_exists_le (α := αᵒᵈ) hs ht
lemma sSup_iUnion_Iic (f : ι → α) : sSup (⋃ (i : ι), Iic (f i)) = ⨆ i, f i := by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨f i, mem_range_self _, hi⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨f i, mem_iUnion_of_mem i le_rfl, le_rfl⟩
lemma sInf_iUnion_Ici (f : ι → α) : sInf (⋃ (i : ι), Ici (f i)) = ⨅ i, f i :=
  sSup_iUnion_Iic (α := αᵒᵈ) f
theorem csInf_eq_bot_of_bot_mem [OrderBot α] {s : Set α} (hs : ⊥ ∈ s) : sInf s = ⊥ :=
  eq_bot_iff.2 <| csInf_le (OrderBot.bddBelow s) hs
theorem csSup_eq_top_of_top_mem [OrderTop α] {s : Set α} (hs : ⊤ ∈ s) : sSup s = ⊤ :=
  csInf_eq_bot_of_bot_mem (α := αᵒᵈ) hs
open Function
variable [WellFoundedLT α]
theorem sInf_eq_argmin_on (hs : s.Nonempty) : sInf s = argminOn id wellFounded_lt s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _ _, fun _ ha => argminOn_le id _ _ ha⟩
theorem isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s) := by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _ _, fun a ha => argminOn_le id _ _ ha⟩
theorem le_csInf_iff' (hs : s.Nonempty) : b ≤ sInf s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_csInf hs).isGLB
theorem csInf_mem (hs : s.Nonempty) : sInf s ∈ s :=
  (isLeast_csInf hs).1
theorem MonotoneOn.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm
theorem Monotone.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm
end ConditionallyCompleteLinearOrder
section ConditionallyCompleteLinearOrderBot
@[simp]
theorem csInf_univ [ConditionallyCompleteLinearOrder α] [OrderBot α] : sInf (univ : Set α) = ⊥ :=
  isLeast_univ.csInf_eq
variable [ConditionallyCompleteLinearOrderBot α] {s : Set α} {a : α}
@[simp]
theorem csSup_empty : (sSup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.csSup_empty
theorem isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csSup_empty, isLUB_empty]
  · exact isLUB_csSup hne hs
theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csSup' hs)
theorem csSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
  (csSup_le_iff' ⟨a, h⟩).2 h
theorem lt_csSup_iff' (hb : BddAbove s) : a < sSup s ↔ ∃ b ∈ s, a < b := by
  simpa only [not_le, not_forall₂, exists_prop] using (csSup_le_iff' hb).not
theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩
theorem le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ sInf s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_csInf_iff (OrderBot.bddBelow _) ne
theorem csInf_le' (h : a ∈ s) : sInf s ≤ a := csInf_le (OrderBot.bddBelow _) h
theorem exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : ∃ b ∈ s, a < b := by
  contrapose! h
  exact csSup_le' h
theorem not_mem_of_lt_csInf' {x : α} {s : Set α} (h : x < sInf s) : x ∉ s :=
  not_mem_of_lt_csInf h (OrderBot.bddBelow s)
theorem csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : sInf s ≤ sInf t :=
  csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂
theorem csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s ⊆ t) : sSup s ≤ sSup t := by
  rcases eq_empty_or_nonempty s with rfl | h
  · rw [csSup_empty]
    exact bot_le
  · exact csSup_le_csSup h₁ h h₂
end ConditionallyCompleteLinearOrderBot
namespace WithTop
variable [ConditionallyCompleteLinearOrderBot α]
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  classical
  constructor
  · show ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply coe_le_coe.2
      exact le_csSup h₂ ha
    · intro _ _
      exact le_top
  · show ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine coe_le_coe.2 (csSup_le ?_ ?_)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact coe_le_coe.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact coe_le_coe.1 (hb ha)
theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    dsimp only [sSup]
    show IsLUB ∅ _
    split_ifs with h₁ h₂
    · cases h₁
    · rw [preimage_empty, csSup_empty]
      exact isLUB_empty
    · exfalso
      apply h₂
      use ⊥
      rintro a ⟨⟩
  exact isLUB_sSup' hs
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  classical
  constructor
  · show ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine coe_le_coe.2 (csInf_le ?_ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff, ← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact coe_le_coe.1 (hb hc)
  · show ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine coe_le_coe.2 (le_csInf ?_ ?_)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (not_nonempty_iff_eq_empty.2 h ⟨a, ha⟩).elim
        · intro b hb
          rw [← coe_le_coe]
          exact ha hb
theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) := by
  by_cases hs : BddBelow s
  · exact isGLB_sInf' hs
  · exfalso
    apply hs
    use ⊥
    intro _ _
    exact bot_le
noncomputable instance : CompleteLinearOrder (WithTop α) where
  __ := linearOrder
  __ := LinearOrder.toBiheytingAlgebra
  le_sSup s := (isLUB_sSup s).1
  sSup_le s := (isLUB_sSup s).2
  le_sInf s := (isGLB_sInf s).2
  sInf_le s := (isGLB_sInf s).1
@[norm_cast]
theorem coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sSup' hb, sSup_image]
@[norm_cast]
theorem coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sInf' hs h's, sInf_image]
end WithTop
namespace Monotone
variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)
include h_mono
theorem le_csSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ sSup (f '' s) :=
  le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)
theorem csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    sSup (f '' s) ≤ f B :=
  csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)
theorem csInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    sInf (f '' s) ≤ f c := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact le_csSup_image (α := αᵒᵈ) (β := βᵒᵈ)
    (show Monotone f' from fun x y hxy => h_mono hxy) hcs h_bdd
theorem le_csInf_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ sInf (f '' s) := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact csSup_image_le (α := αᵒᵈ) (β := βᵒᵈ)
    (show Monotone f' from fun x y hxy => h_mono hxy) hs hB
end Monotone
section
variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [ConditionallyCompleteLattice γ] {s : Set α} {t : Set β}
variable {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}
theorem csSup_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup (image2 l s t) = l (sSup s) (sSup t) := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [csSup_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁)
      (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, csSup_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, csSup_le_iff hs₁ hs₀]
theorem csSup_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sSup s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (β := βᵒᵈ) h₁ h₂
theorem csSup_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sSup (image2 l s t) = l (sInf s) (sSup t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) h₁ h₂
theorem csSup_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sInf s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂
theorem csInf_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sInf s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) (γ := γᵒᵈ) (u₁ := l₁) (u₂ := l₂)
    (fun _ => (h₁ _).dual) fun _ => (h₂ _).dual
theorem csInf_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sInf s) (sSup t) :=
  csInf_image2_eq_csInf_csInf (β := βᵒᵈ) h₁ h₂
theorem csInf_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sSup s) (sInf t) :=
  csInf_image2_eq_csInf_csInf (α := αᵒᵈ) h₁ h₂
theorem csInf_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sSup s) (sSup t) :=
  csInf_image2_eq_csInf_csInf (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂
end
section WithTopBot
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) :=
  { lattice, instSupSet, instInfSet with
    le_csSup := fun _ a _ haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    csSup_le := fun _ _ hS haS => (WithTop.isLUB_sSup' hS).2 haS
    csInf_le := fun _ _ hS haS => (WithTop.isGLB_sInf' hS).1 haS
    le_csInf := fun _ a _ haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice with
    le_csSup := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).csInf_le
    csSup_le := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).le_csInf
    csInf_le := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).le_csSup
    le_csInf := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).csSup_le }
open Classical in
noncomputable instance WithTop.WithBot.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) :=
  { instInfSet, instSupSet, boundedOrder, lattice with
    le_sSup := fun _ a haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    sSup_le := fun S a ha => by
      rcases S.eq_empty_or_nonempty with h | h
      · show ite _ _ _ ≤ a
        split_ifs with h₁ h₂
        · rw [h] at h₁
          cases h₁
        · convert bot_le (a := a)
          apply congr_arg
          simp only [h, preimage_empty, WithBot.sSup_empty]
        · exfalso
          apply h₂
          use ⊥
          rw [h]
          rintro b ⟨⟩
      · exact (WithTop.isLUB_sSup' h).2 ha
    sInf_le := fun S a haS =>
      show ite _ _ _ ≤ a by
        simp only [OrderBot.bddBelow, not_true_eq_false, or_false]
        split_ifs with h₁
        · cases' a with a
          · exact le_rfl
          cases h₁ haS
        · cases a
          · exact le_top
          · apply WithTop.coe_le_coe.2
            refine csInf_le ?_ haS
            use ⊥
            intro b _
            exact bot_le
    le_sInf := fun _ a haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }
noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithTop (WithBot α)) :=
  { completeLattice, linearOrder, LinearOrder.toBiheytingAlgebra with }
noncomputable instance WithBot.WithTop.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithBot (WithTop α)) :=
  { instInfSet, instSupSet, instBoundedOrder, lattice with
    le_sSup := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).sInf_le
    sSup_le := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).le_sInf
    sInf_le := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).le_sSup
    le_sInf := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).sSup_le }
noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) :=
  { completeLattice, linearOrder, LinearOrder.toBiheytingAlgebra with }
end WithTopBot