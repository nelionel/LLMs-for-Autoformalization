import Mathlib.Data.Set.Basic
class Btw (α : Type*) where
  btw : α → α → α → Prop
export Btw (btw)
class SBtw (α : Type*) where
  sbtw : α → α → α → Prop
export SBtw (sbtw)
class CircularPreorder (α : Type*) extends Btw α, SBtw α where
  btw_refl (a : α) : btw a a a
  btw_cyclic_left {a b c : α} : btw a b c → btw b c a
  sbtw := fun a b c => btw a b c ∧ ¬btw c b a
  sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a := by intros; rfl
  sbtw_trans_left {a b c d : α} : sbtw a b c → sbtw b d c → sbtw a d c
export CircularPreorder (btw_refl btw_cyclic_left sbtw_trans_left)
class CircularPartialOrder (α : Type*) extends CircularPreorder α where
  btw_antisymm {a b c : α} : btw a b c → btw c b a → a = b ∨ b = c ∨ c = a
export CircularPartialOrder (btw_antisymm)
class CircularOrder (α : Type*) extends CircularPartialOrder α where
  btw_total : ∀ a b c : α, btw a b c ∨ btw c b a
export CircularOrder (btw_total)
section CircularPreorder
variable {α : Type*} [CircularPreorder α]
theorem btw_rfl {a : α} : btw a a a :=
  btw_refl _
theorem Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : btw b c a :=
  btw_cyclic_left h
theorem btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a b :=
  h.cyclic_left.cyclic_left
alias Btw.btw.cyclic_right := btw_cyclic_right
theorem btw_cyclic {a b c : α} : btw a b c ↔ btw c a b :=
  ⟨btw_cyclic_right, btw_cyclic_left⟩
theorem sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a :=
  CircularPreorder.sbtw_iff_btw_not_btw
theorem btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c :=
  (sbtw_iff_btw_not_btw.1 h).1
alias SBtw.sbtw.btw := btw_of_sbtw
theorem not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
  (sbtw_iff_btw_not_btw.1 h).2
alias SBtw.sbtw.not_btw := not_btw_of_sbtw
theorem not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a := fun h' => h'.not_btw h
alias Btw.btw.not_sbtw := not_sbtw_of_btw
theorem sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
  sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩
alias Btw.btw.sbtw_of_not_btw := sbtw_of_btw_not_btw
theorem sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a :=
  h.btw.cyclic_left.sbtw_of_not_btw fun h' => h.not_btw h'.cyclic_left
alias SBtw.sbtw.cyclic_left := sbtw_cyclic_left
theorem sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
  h.cyclic_left.cyclic_left
alias SBtw.sbtw.cyclic_right := sbtw_cyclic_right
theorem sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b :=
  ⟨sbtw_cyclic_right, sbtw_cyclic_left⟩
theorem SBtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c) : sbtw b d c → sbtw a d c :=
  sbtw_trans_left h
theorem sbtw_trans_right {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d) : sbtw a b d :=
  (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right
alias SBtw.sbtw.trans_right := sbtw_trans_right
theorem sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬sbtw c b a :=
  h.btw.not_sbtw
alias SBtw.sbtw.not_sbtw := sbtw_asymm
theorem sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a := fun h => h.not_btw h.btw
theorem sbtw_irrefl_left {a b : α} : ¬sbtw a a b := fun h => sbtw_irrefl_left_right h.cyclic_left
theorem sbtw_irrefl_right {a b : α} : ¬sbtw a b b := fun h => sbtw_irrefl_left_right h.cyclic_right
theorem sbtw_irrefl (a : α) : ¬sbtw a a a :=
  sbtw_irrefl_left_right
end CircularPreorder
section CircularPartialOrder
variable {α : Type*} [CircularPartialOrder α]
theorem Btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a → a = b ∨ b = c ∨ c = a :=
  btw_antisymm h
end CircularPartialOrder
section CircularOrder
variable {α : Type*} [CircularOrder α]
theorem btw_refl_left_right (a b : α) : btw a b a :=
  or_self_iff.1 (btw_total a b a)
theorem btw_rfl_left_right {a b : α} : btw a b a :=
  btw_refl_left_right _ _
theorem btw_refl_left (a b : α) : btw a a b :=
  btw_rfl_left_right.cyclic_right
theorem btw_rfl_left {a b : α} : btw a a b :=
  btw_refl_left _ _
theorem btw_refl_right (a b : α) : btw a b b :=
  btw_rfl_left_right.cyclic_left
theorem btw_rfl_right {a b : α} : btw a b b :=
  btw_refl_right _ _
theorem sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a := by
  rw [sbtw_iff_btw_not_btw]
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left
theorem btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬sbtw c b a :=
  iff_not_comm.1 sbtw_iff_not_btw
end CircularOrder
namespace Set
section CircularPreorder
variable {α : Type*} [CircularPreorder α]
def cIcc (a b : α) : Set α :=
  { x | btw a x b }
def cIoo (a b : α) : Set α :=
  { x | sbtw a x b }
@[simp]
theorem mem_cIcc {a b x : α} : x ∈ cIcc a b ↔ btw a x b :=
  Iff.rfl
@[simp]
theorem mem_cIoo {a b x : α} : x ∈ cIoo a b ↔ sbtw a x b :=
  Iff.rfl
end CircularPreorder
section CircularOrder
variable {α : Type*} [CircularOrder α]
theorem left_mem_cIcc (a b : α) : a ∈ cIcc a b :=
  btw_rfl_left
theorem right_mem_cIcc (a b : α) : b ∈ cIcc a b :=
  btw_rfl_right
theorem compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a := by
  ext
  rw [Set.mem_cIoo, sbtw_iff_not_btw, cIcc, mem_compl_iff, mem_setOf]
theorem compl_cIoo {a b : α} : (cIoo a b)ᶜ = cIcc b a := by
  ext
  rw [Set.mem_cIcc, btw_iff_not_sbtw, cIoo, mem_compl_iff, mem_setOf]
end CircularOrder
end Set
abbrev LE.toBtw (α : Type*) [LE α] : Btw α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
abbrev LT.toSBtw (α : Type*) [LT α] : SBtw α where
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
abbrev Preorder.toCircularPreorder (α : Type*) [Preorder α] : CircularPreorder α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl _ := Or.inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left {a b c} h := by
    dsimp
    rwa [← or_assoc, or_comm]
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩)
    · exact Or.inl ⟨hab.trans hbd, hdc⟩
    · exact (hbc.not_lt hcb).elim
    · exact (hbc.not_lt hcb).elim
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact (hbc.not_lt hcb).elim
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact Or.inr (Or.inr ⟨hca, hab.trans hbd⟩)
  sbtw_iff_btw_not_btw {a b c} := by
    simp_rw [lt_iff_le_not_le]
    have h1 := le_trans a b c
    have h2 := le_trans b c a
    have h3 := le_trans c a b
    revert h1 h2 h3
    generalize (a ≤ b) = p1
    generalize (b ≤ a) = p2
    generalize (a ≤ c) = p3
    generalize (c ≤ a) = p4
    generalize (b ≤ c) = p5
    by_cases p1 <;> by_cases p2 <;> by_cases p3 <;> by_cases p4 <;> by_cases p5 <;> simp [*]
abbrev PartialOrder.toCircularPartialOrder (α : Type*) [PartialOrder α] : CircularPartialOrder α :=
  { Preorder.toCircularPreorder α with
    btw_antisymm := fun {a b c} => by
      rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inr <| hca.antisymm hac)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inr <| hca.antisymm hac) }
abbrev LinearOrder.toCircularOrder (α : Type*) [LinearOrder α] : CircularOrder α :=
  { PartialOrder.toCircularPartialOrder α with
    btw_total := fun a b c => by
      rcases le_total a b with hab | hba <;> rcases le_total b c with hbc | hcb <;>
        rcases le_total c a with hca | hac
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inr <| Or.inr ⟨hca, hab⟩)
      · exact Or.inr (Or.inr <| Or.inr ⟨hac, hcb⟩)
      · exact Or.inl (Or.inr <| Or.inl ⟨hbc, hca⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩)
      · exact Or.inr (Or.inl ⟨hcb, hba⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩) }
namespace OrderDual
instance btw (α : Type*) [Btw α] : Btw αᵒᵈ :=
  ⟨fun a b c : α => Btw.btw c b a⟩
instance sbtw (α : Type*) [SBtw α] : SBtw αᵒᵈ :=
  ⟨fun a b c : α => SBtw.sbtw c b a⟩
instance circularPreorder (α : Type*) [CircularPreorder α] : CircularPreorder αᵒᵈ :=
  { OrderDual.btw α,
    OrderDual.sbtw α with
    btw_refl := fun _ => @btw_refl α _ _
    btw_cyclic_left := fun {_ _ _} => @btw_cyclic_right α _ _ _ _
    sbtw_trans_left := fun {_ _ _ _} habc hbdc => hbdc.trans_right habc
    sbtw_iff_btw_not_btw := fun {a b c} => @sbtw_iff_btw_not_btw α _ c b a }
instance circularPartialOrder (α : Type*) [CircularPartialOrder α] : CircularPartialOrder αᵒᵈ :=
  { OrderDual.circularPreorder α with
    btw_antisymm := fun {_ _ _} habc hcba => @btw_antisymm α _ _ _ _ hcba habc }
instance (α : Type*) [CircularOrder α] : CircularOrder αᵒᵈ :=
  { OrderDual.circularPartialOrder α with
    btw_total := fun {a b c} => @btw_total α _ c b a }
end OrderDual