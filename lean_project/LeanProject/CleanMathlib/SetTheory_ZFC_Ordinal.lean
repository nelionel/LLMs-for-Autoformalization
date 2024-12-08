import Mathlib.Order.RelIso.Set
import Mathlib.SetTheory.ZFC.Basic
universe u
variable {x y z : ZFSet.{u}}
namespace ZFSet
def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x
@[simp]
theorem isTransitive_empty : IsTransitive ∅ := fun y hy => (not_mem_empty y hy).elim
@[deprecated isTransitive_empty (since := "2024-09-21")]
alias empty_isTransitive := isTransitive_empty
theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x := h y
theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : ZFSet}, x ∈ y → y ∈ z → x ∈ z :=
  ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩
alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans
protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∩ y).IsTransitive := fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩
protected theorem IsTransitive.sUnion (h : x.IsTransitive) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)
theorem IsTransitive.sUnion' (H : ∀ y ∈ x, IsTransitive y) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw
protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'
protected theorem IsTransitive.powerset (h : x.IsTransitive) : (powerset x).IsTransitive :=
  fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)
theorem isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) ⊆ x := by
  constructor <;>
  intro h y hy
  · obtain ⟨z, hz, hz'⟩ := mem_sUnion.1 hy
    exact h.mem_trans hz' hz
  · exact fun z hz ↦ h <| mem_sUnion_of_mem hz hy
alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset
theorem isTransitive_iff_subset_powerset : x.IsTransitive ↔ x ⊆ powerset x :=
  ⟨fun h _ hy => mem_powerset.2 <| h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩
alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset
structure IsOrdinal (x : ZFSet) : Prop where
  isTransitive : x.IsTransitive
  mem_trans' {y z w : ZFSet} : y ∈ z → z ∈ w → w ∈ x → y ∈ w
namespace IsOrdinal
theorem subset_of_mem (h : x.IsOrdinal) : y ∈ x → y ⊆ x :=
  h.isTransitive.subset_of_mem
theorem mem_trans (h : z.IsOrdinal) : x ∈ y → y ∈ z → x ∈ z :=
  h.isTransitive.mem_trans
protected theorem isTrans (h : x.IsOrdinal) : IsTrans x.toSet (Subrel (· ∈ ·) _) :=
  ⟨fun _ _ c hab hbc => h.mem_trans' hab hbc c.2⟩
end IsOrdinal
theorem isOrdinal_iff_isTrans :
    x.IsOrdinal ↔ x.IsTransitive ∧ IsTrans x.toSet (Subrel (· ∈ ·) _) := by
  use fun h => ⟨h.isTransitive, h.isTrans⟩
  rintro ⟨h₁, ⟨h₂⟩⟩
  use h₁
  intro y z w hyz hzw hwx
  have hzx := h₁.mem_trans hzw hwx
  exact h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw
end ZFSet