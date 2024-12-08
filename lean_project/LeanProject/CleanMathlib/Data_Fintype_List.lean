import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Permutation
variable {α : Type*} [DecidableEq α]
open List
namespace Multiset
def lists : Multiset α → Finset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations.toFinset) fun l l' (h : l ~ l') => by
    ext sl
    simp only [mem_permutations, List.mem_toFinset]
    exact ⟨fun hs => hs.trans h, fun hs => hs.trans h.symm⟩
@[simp]
theorem lists_coe (l : List α) : lists (l : Multiset α) = l.permutations.toFinset :=
  rfl
@[simp]
theorem mem_lists_iff (s : Multiset α) (l : List α) : l ∈ lists s ↔ s = ⟦l⟧ := by
  induction s using Quotient.inductionOn
  simpa using perm_comm
end Multiset
instance fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup } :=
  Fintype.subtype ((Finset.univ : Finset α).powerset.biUnion fun s => s.val.lists) fun l => by
    suffices (∃ a : Finset α, a.val = ↑l) ↔ l.Nodup by simpa
    constructor
    · rintro ⟨s, hs⟩
      simpa [← Multiset.coe_nodup, ← hs] using s.nodup
    · intro hl
      refine ⟨⟨↑l, hl⟩, ?_⟩
      simp