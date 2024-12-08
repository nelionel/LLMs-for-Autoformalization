import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Set.SymmDiff
assert_not_exists List.sublistsLen
assert_not_exists Multiset.powerset
assert_not_exists CompleteLattice
assert_not_exists OrderedCommMonoid
open Multiset Subtype Function
universe u
variable {α : Type*} {β : Type*} {γ : Type*}
namespace Finset
section SymmDiff
open scoped symmDiff
variable [DecidableEq α] {s t : Finset α} {a b : α}
theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]
@[simp, norm_cast]
theorem coe_symmDiff : (↑(s ∆ t) : Set α) = (s : Set α) ∆ t :=
  Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]
@[simp] lemma symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t := symmDiff_eq_bot
@[simp] lemma symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not
end SymmDiff
end Finset