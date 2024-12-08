import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
open Function OrderDual Set
variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}
@[ext (flat := false)]
structure NonemptyInterval (α : Type*) [LE α] extends Prod α α where
  fst_le_snd : fst ≤ snd
namespace NonemptyInterval
section LE
variable [LE α] {s t : NonemptyInterval α}
theorem toProd_injective : Injective (toProd : NonemptyInterval α → α × α) :=
  fun s t h => by cases s; cases t; congr
def toDualProd : NonemptyInterval α → αᵒᵈ × α :=
  toProd
@[simp]
theorem toDualProd_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, s.snd) :=
  rfl
theorem toDualProd_injective : Injective (toDualProd : NonemptyInterval α → αᵒᵈ × α) :=
  toProd_injective
instance [IsEmpty α] : IsEmpty (NonemptyInterval α) :=
  ⟨fun s => isEmptyElim s.fst⟩
instance [Subsingleton α] : Subsingleton (NonemptyInterval α) :=
  toDualProd_injective.subsingleton
instance le : LE (NonemptyInterval α) :=
  ⟨fun s t => t.fst ≤ s.fst ∧ s.snd ≤ t.snd⟩
theorem le_def : s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd :=
  Iff.rfl
@[simps]
def toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α where
  toFun := toDualProd
  inj' := toDualProd_injective
  map_rel_iff' := Iff.rfl
def dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ where
  toFun s := ⟨s.toProd.swap, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.swap, s.fst_le_snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simp]
theorem fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd :=
  rfl
@[simp]
theorem snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst :=
  rfl
end LE
section Preorder
variable [Preorder α] [Preorder β] [Preorder γ] {s : NonemptyInterval α} {x : α × α} {a : α}
instance : Preorder (NonemptyInterval α) :=
  Preorder.lift toDualProd
instance : Coe (NonemptyInterval α) (Set α) :=
  ⟨fun s => Icc s.fst s.snd⟩
instance (priority := 100) : Membership α (NonemptyInterval α) :=
  ⟨fun s a => a ∈ (s : Set α)⟩
@[simp]
theorem mem_mk {hx : x.1 ≤ x.2} : a ∈ mk x hx ↔ x.1 ≤ a ∧ a ≤ x.2 :=
  Iff.rfl
theorem mem_def : a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd :=
  Iff.rfl
theorem coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty :=
  nonempty_Icc.2 s.fst_le_snd
@[simps]
def pure (a : α) : NonemptyInterval α :=
  ⟨⟨a, a⟩, le_rfl⟩
theorem mem_pure_self (a : α) : a ∈ pure a :=
  ⟨le_rfl, le_rfl⟩
theorem pure_injective : Injective (pure : α → NonemptyInterval α) := fun _ _ =>
  congr_arg <| Prod.fst ∘ toProd
@[simp]
theorem dual_pure (a : α) : dual (pure a) = pure (toDual a) :=
  rfl
instance [Inhabited α] : Inhabited (NonemptyInterval α) :=
  ⟨pure default⟩
instance [Nonempty α] : Nonempty (NonemptyInterval α) :=
  Nonempty.map pure (by infer_instance)
instance [Nontrivial α] : Nontrivial (NonemptyInterval α) :=
  pure_injective.nontrivial
@[simps!]
def map (f : α →o β) (a : NonemptyInterval α) : NonemptyInterval β :=
  ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩
@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (a : NonemptyInterval α) :
    (a.map f).map g = a.map (g.comp f) :=
  rfl
@[simp]
theorem dual_map (f : α →o β) (a : NonemptyInterval α) :
    dual (a.map f) = a.dual.map f.dual :=
  rfl
@[simps]
def map₂ (f : α → β → γ) (h₀ : ∀ b, Monotone fun a => f a b) (h₁ : ∀ a, Monotone (f a)) :
    NonemptyInterval α → NonemptyInterval β → NonemptyInterval γ := fun s t =>
  ⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans <| h₁ _ t.fst_le_snd⟩
@[simp]
theorem map₂_pure (f : α → β → γ) (h₀ h₁) (a : α) (b : β) :
    map₂ f h₀ h₁ (pure a) (pure b) = pure (f a b) :=
  rfl
@[simp]
theorem dual_map₂ (f : α → β → γ) (h₀ h₁ s t) :
    dual (map₂ f h₀ h₁ s t) =
      map₂ (fun a b => toDual <| f (ofDual a) <| ofDual b) (fun _ => (h₀ _).dual)
        (fun _ => (h₁ _).dual) (dual s) (dual t) :=
  rfl
variable [BoundedOrder α]
instance : OrderTop (NonemptyInterval α) where
  top := ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top _ := ⟨bot_le, le_top⟩
@[simp]
theorem dual_top : dual (⊤ : NonemptyInterval α) = ⊤ :=
  rfl
end Preorder
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {s t : NonemptyInterval α} {a b : α}
instance : PartialOrder (NonemptyInterval α) :=
  PartialOrder.lift _ toDualProd_injective
def coeHom : NonemptyInterval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff (fun s => Icc s.fst s.snd) fun s _ => Icc_subset_Icc_iff s.fst_le_snd
instance setLike : SetLike (NonemptyInterval α) α where
  coe s := Icc s.fst s.snd
  coe_injective' := coeHom.injective
@[norm_cast] 
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ (s : NonemptyInterval α) ≤ t :=
  (@coeHom α _).le_iff_le
@[norm_cast] 
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
@[simp]
theorem coe_coeHom : (coeHom : NonemptyInterval α → Set α) = ((↑) : NonemptyInterval α → Set α) :=
  rfl
theorem coe_def (s : NonemptyInterval α) : (s : Set α) = Set.Icc s.toProd.1 s.toProd.2 := rfl
@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _
@[simp]
theorem mem_pure : b ∈ pure a ↔ b = a := by
  rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]
@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ :=
  Icc_bot_top
@[simp, norm_cast]
theorem coe_dual (s : NonemptyInterval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s :=
  dual_Icc
theorem subset_coe_map (f : α →o β) (s : NonemptyInterval α) : f '' s ⊆ s.map f :=
  image_subset_iff.2 fun _ ha => ⟨f.mono ha.1, f.mono ha.2⟩
end PartialOrder
section Lattice
variable [Lattice α]
instance : Max (NonemptyInterval α) :=
  ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans <| s.fst_le_snd.trans le_sup_left⟩⟩
instance : SemilatticeSup (NonemptyInterval α) :=
  toDualProd_injective.semilatticeSup _ fun _ _ => rfl
@[simp]
theorem fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst :=
  rfl
@[simp]
theorem snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd :=
  rfl
end Lattice
end NonemptyInterval
abbrev Interval (α : Type*) [LE α] :=
  WithBot (NonemptyInterval α) 
namespace Interval
section LE
variable [LE α]
instance : Inhabited (Interval α) := WithBot.inhabited
instance : LE (Interval α) := WithBot.le
instance : OrderBot (Interval α) := WithBot.orderBot
instance : Coe (NonemptyInterval α) (Interval α) :=
  WithBot.coe
instance canLift : CanLift (Interval α) (NonemptyInterval α) (↑) fun r => r ≠ ⊥ :=
  WithBot.canLift
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : Interval α → Sort*} (bot : C ⊥) (coe : ∀ a : NonemptyInterval α, C a) :
    ∀ n : Interval α, C n :=
  WithBot.recBotCoe bot coe
theorem coe_injective : Injective ((↑) : NonemptyInterval α → Interval α) :=
  WithBot.coe_injective
@[norm_cast] 
theorem coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t :=
  WithBot.coe_inj
protected
theorem «forall» {p : Interval α → Prop} : (∀ s, p s) ↔ p ⊥ ∧ ∀ s : NonemptyInterval α, p s :=
  Option.forall
protected
theorem «exists» {p : Interval α → Prop} : (∃ s, p s) ↔ p ⊥ ∨ ∃ s : NonemptyInterval α, p s :=
  Option.exists
instance [IsEmpty α] : Unique (Interval α) :=
  inferInstanceAs <| Unique (Option _)
def dual : Interval α ≃ Interval αᵒᵈ :=
  NonemptyInterval.dual.optionCongr
end LE
section Preorder
variable [Preorder α] [Preorder β] [Preorder γ]
instance : Preorder (Interval α) :=
  WithBot.preorder
def pure (a : α) : Interval α :=
  NonemptyInterval.pure a
theorem pure_injective : Injective (pure : α → Interval α) :=
  coe_injective.comp NonemptyInterval.pure_injective
@[simp]
theorem dual_pure (a : α) : dual (pure a) = pure (toDual a) :=
  rfl
@[simp]
theorem dual_bot : dual (⊥ : Interval α) = ⊥ :=
  rfl
@[simp]
theorem pure_ne_bot {a : α} : pure a ≠ ⊥ :=
  WithBot.coe_ne_bot
@[simp]
theorem bot_ne_pure {a : α} : ⊥ ≠ pure a :=
  WithBot.bot_ne_coe
instance [Nonempty α] : Nontrivial (Interval α) :=
  Option.nontrivial
def map (f : α →o β) : Interval α → Interval β :=
  WithBot.map (NonemptyInterval.map f)
@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (s : Interval α) : (s.map f).map g = s.map (g.comp f) :=
  Option.map_map _ _ _
@[simp]
theorem dual_map (f : α →o β) (s : Interval α) : dual (s.map f) = s.dual.map f.dual := by
  cases s
  · rfl
  · exact WithBot.map_comm rfl _
variable [BoundedOrder α]
instance boundedOrder : BoundedOrder (Interval α) :=
  WithBot.instBoundedOrder
@[simp]
theorem dual_top : dual (⊤ : Interval α) = ⊤ :=
  rfl
end Preorder
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {s t : Interval α} {a b : α}
instance partialOrder : PartialOrder (Interval α) :=
  WithBot.partialOrder
def coeHom : Interval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, _ => iff_of_true bot_le bot_le
    | some s, ⊥ =>
      iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some _, some _ => (@NonemptyInterval.coeHom α _).le_iff_le.trans WithBot.coe_le_coe.symm
instance setLike : SetLike (Interval α) α where
  coe := coeHom
  coe_injective' := coeHom.injective
@[norm_cast] 
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le
@[norm_cast] 
theorem coe_sSubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _
@[simp, norm_cast]
theorem coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s :=
  rfl
@[simp, norm_cast]
theorem coe_bot : ((⊥ : Interval α) : Set α) = ∅ :=
  rfl
@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ :=
  Icc_bot_top
@[simp, norm_cast]
theorem coe_dual (s : Interval α) : (dual s : Set αᵒᵈ) = ofDual ⁻¹' s := by
  cases s with
  | bot => rfl
  | coe s₀ => exact NonemptyInterval.coe_dual s₀
theorem subset_coe_map (f : α →o β) : ∀ s : Interval α, f '' s ⊆ s.map f
  | ⊥ => by simp
  | (s : NonemptyInterval α) => s.subset_coe_map _
@[simp]
theorem mem_pure : b ∈ pure a ↔ b = a := by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]
theorem mem_pure_self (a : α) : a ∈ pure a :=
  mem_pure.2 rfl
end PartialOrder
section Lattice
variable [Lattice α]
instance semilatticeSup : SemilatticeSup (Interval α) :=
  WithBot.semilatticeSup
section Decidable
variable [@DecidableRel α (· ≤ ·)]
instance lattice : Lattice (Interval α) :=
  { Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, _ => ⊥
      | _, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then
          WithBot.some
            ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
              sup_le (le_inf s.fst_le_snd h.1) <| le_inf h.2 t.fst_le_snd⟩
        else ⊥
    inf_le_left := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some _ => bot_le
      | some _, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.coe_le_coe.2 ⟨le_sup_left, inf_le_left⟩
        · exact bot_le
    inf_le_right := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some _ => bot_le
      | some _, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.coe_le_coe.2 ⟨le_sup_right, inf_le_right⟩
        · exact bot_le
    le_inf := fun s t c =>
      match s, t, c with
      | ⊥, _, _ => fun _ _ => bot_le
      | (s : NonemptyInterval α), t, c => fun hb hc => by
        lift t to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hb
        lift c to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hc
        change _ ≤ dite _ _ _
        simp only [WithBot.coe_le_coe] at hb hc ⊢
        rw [dif_pos, WithBot.coe_le_coe]
        · exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩
        rcases hb with ⟨hb₁, hb₂⟩
        rcases hc with ⟨hc₁, hc₂⟩
        change t.toProd.fst ≤ s.toProd.fst at hb₁
        change s.toProd.snd ≤ t.toProd.snd at hb₂
        change c.toProd.fst ≤ s.toProd.fst at hc₁
        change s.toProd.snd ≤ c.toProd.snd at hc₂
        exact ⟨hb₁.trans <| s.fst_le_snd.trans hc₂, hc₁.trans <| s.fst_le_snd.trans hb₂⟩ }
@[simp, norm_cast]
theorem coe_inf : ∀ s t : Interval α, (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t
  | ⊥, _ => by
    rw [bot_inf_eq]
    exact (empty_inter _).symm
  | (s : NonemptyInterval α), ⊥ => by
    rw [inf_bot_eq]
    exact (inter_empty _).symm
  | (s : NonemptyInterval α), (t : NonemptyInterval α) => by
    simp only [Min.min, coe_coe, NonemptyInterval.coe_def, Icc_inter_Icc,
      SemilatticeInf.inf, Lattice.inf]
    split_ifs with h
    · simp only [coe_coe, NonemptyInterval.coe_def]
    · refine (Icc_eq_empty <| mt ?_ h).symm
      exact fun h ↦ ⟨le_sup_left.trans <| h.trans inf_le_right,
        le_sup_right.trans <| h.trans inf_le_left⟩
end Decidable
@[simp, norm_cast]
theorem disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t := by
  classical
    rw [disjoint_iff_inf_le, disjoint_iff_inf_le, ← coe_subset_coe, coe_inf]
    rfl
end Lattice
end Interval
namespace NonemptyInterval
section Preorder
variable [Preorder α] {s : NonemptyInterval α} {a : α}
@[simp, norm_cast]
theorem coe_pure_interval (a : α) : (pure a : Interval α) = Interval.pure a :=
  rfl
@[simp, norm_cast]
theorem coe_eq_pure : (s : Interval α) = Interval.pure a ↔ s = pure a := by
  rw [← Interval.coe_inj, coe_pure_interval]
@[simp, norm_cast]
theorem coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α) = ⊤ :=
  rfl
end Preorder
@[simp, norm_cast]
theorem mem_coe_interval [PartialOrder α] {s : NonemptyInterval α} {x : α} :
    x ∈ (s : Interval α) ↔ x ∈ s :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_sup_interval [Lattice α] (s t : NonemptyInterval α) :
    (↑(s ⊔ t) : Interval α) = ↑s ⊔ ↑t :=
  rfl
end NonemptyInterval
namespace Interval
section CompleteLattice
variable [CompleteLattice α]
noncomputable instance completeLattice [@DecidableRel α (· ≤ ·)] :
    CompleteLattice (Interval α) := by
  classical
  exact
      { Interval.lattice, Interval.boundedOrder with
        sSup := fun S =>
          if h : S ⊆ {⊥} then ⊥
          else
            WithBot.some
              ⟨⟨⨅ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.fst,
                  ⨆ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.snd⟩, by
                obtain ⟨s, hs, ha⟩ := not_subset.1 h
                lift s to NonemptyInterval α using ha
                exact iInf₂_le_of_le s hs (le_iSup₂_of_le s hs s.fst_le_snd)⟩
        le_sSup := fun s s ha => by
          dsimp only 
          split_ifs with h
          · exact (h ha).le
          cases s
          · exact bot_le
          · 
            apply WithBot.coe_le_coe.2
            constructor
            · apply iInf₂_le
              exact ha
            · exact le_iSup₂_of_le _ ha le_rfl
        sSup_le := fun s s ha => by
          dsimp only 
          split_ifs with h
          · exact bot_le
          obtain ⟨b, hs, hb⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ne_bot_of_le_ne_bot hb (ha _ hs)
          exact
            WithBot.coe_le_coe.2
              ⟨le_iInf₂ fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).1,
                iSup₂_le fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).2⟩
        sInf := fun S =>
          if h :
              ⊥ ∉ S ∧
                ∀ ⦃s : NonemptyInterval α⦄,
                  ↑s ∈ S → ∀ ⦃t : NonemptyInterval α⦄, ↑t ∈ S → s.fst ≤ t.snd then
            WithBot.some
              ⟨⟨⨆ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.fst,
                  ⨅ (s : NonemptyInterval α) (_ : ↑s ∈ S), s.snd⟩,
                iSup₂_le fun s hs => le_iInf₂ <| h.2 hs⟩
          else ⊥
        sInf_le := fun s₁ s ha => by
          dsimp only 
          split_ifs with h
          · lift s to NonemptyInterval α using ne_of_mem_of_not_mem ha h.1
            let f := fun (s : NonemptyInterval α) (_ : ↑s ∈ s₁) => s.toProd.fst
            exact WithBot.coe_le_coe.2 ⟨le_iSup₂ (f := f) s ha, iInf₂_le s ha⟩
          · exact bot_le
        le_sInf := by
          intro S s ha
          cases s with
          | bot => exact bot_le
          | coe s =>
            dsimp 
            split_ifs with h
            · exact WithBot.coe_le_coe.2
                ⟨iSup₂_le fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).1,
                  le_iInf₂ fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).2⟩
            · rw [not_and_or, not_not] at h
              rcases h with h | h
              · exact ha _ h
              · 
                exfalso
                apply h
                intro b hb c hc
                have h₁ := (WithBot.coe_le_coe.1 <| ha _ hb).1
                repeat rw [NonemptyInterval.toDualProd_apply] at h₁
                rw [OrderDual.toDual_le_toDual] at h₁
                exact h₁.trans (s.fst_le_snd.trans (WithBot.coe_le_coe.1 <| ha _ hc).2)
  }
@[simp, norm_cast]
theorem coe_sInf [@DecidableRel α (· ≤ ·)] (S : Set (Interval α)) :
    ↑(sInf S) = ⋂ s ∈ S, (s : Set α) := by
  classical 
  change ((dite _ _ _ : Interval α) : Set α) = ⋂ (s : Interval α) (_ : s ∈ S), (s : Set α)
  split_ifs with h
  · ext
    simp [Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
  simp_rw [not_and_or, Classical.not_not] at h
  rcases h with h | h
  · refine (eq_empty_of_subset_empty ?_).symm
    exact iInter₂_subset_of_subset _ h Subset.rfl
  · refine (not_nonempty_iff_eq_empty.1 ?_).symm
    rintro ⟨x, hx⟩
    rw [mem_iInter₂] at hx
    exact h fun s ha t hb => (hx _ ha).1.trans (hx _ hb).2
@[simp, norm_cast]
theorem coe_iInf [@DecidableRel α (· ≤ ·)] (f : ι → Interval α) :
    ↑(⨅ i, f i) = ⋂ i, (f i : Set α) := by simp [iInf]
@[norm_cast]
theorem coe_iInf₂ [@DecidableRel α (· ≤ ·)] (f : ∀ i, κ i → Interval α) :
    ↑(⨅ (i) (j), f i j) = ⋂ (i) (j), (f i j : Set α) := by simp_rw [coe_iInf]
end CompleteLattice
end Interval