import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Separation.Basic
open Set
variable {α : Type*}
class PriestleySpace (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  priestley {x y : α} : ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U
variable [TopologicalSpace α]
section Preorder
variable [Preorder α] [PriestleySpace α] {x y : α}
theorem exists_isClopen_upper_of_not_le :
    ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U :=
  PriestleySpace.priestley
theorem exists_isClopen_lower_of_not_le (h : ¬x ≤ y) :
    ∃ U : Set α, IsClopen U ∧ IsLowerSet U ∧ x ∉ U ∧ y ∈ U :=
  let ⟨U, hU, hU', hx, hy⟩ := exists_isClopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, Classical.not_not.2 hx, hy⟩
end Preorder
section PartialOrder
variable [PartialOrder α] [PriestleySpace α] {x y : α}
theorem exists_isClopen_upper_or_lower_of_ne (h : x ≠ y) :
    ∃ U : Set α, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x ∈ U ∧ y ∉ U := by
  obtain h | h := h.not_le_or_not_le
  · exact (exists_isClopen_upper_of_not_le h).imp fun _ ↦ And.imp_right <| And.imp_left Or.inl
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_isClopen_lower_of_not_le h
    exact ⟨U, hU, Or.inr hU', hx, hy⟩
instance (priority := 100) PriestleySpace.toT2Space : T2Space α :=
  ⟨fun _ _ h ↦
    let ⟨U, hU, _, hx, hy⟩ := exists_isClopen_upper_or_lower_of_ne h
    ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hx, hy, disjoint_compl_right⟩⟩
end PartialOrder