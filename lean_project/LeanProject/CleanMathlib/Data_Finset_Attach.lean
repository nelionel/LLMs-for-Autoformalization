import Mathlib.Data.Finset.Defs
assert_not_exists List.sublistsLen
assert_not_exists Multiset.powerset
assert_not_exists CompleteLattice
assert_not_exists OrderedCommMonoid
open Multiset Subtype Function
universe u
variable {α : Type*} {β : Type*} {γ : Type*}
namespace Finset
attribute [local trans] Subset.trans Superset.trans
def attach (s : Finset α) : Finset { x // x ∈ s } :=
  ⟨Multiset.attach s.1, nodup_attach.2 s.2⟩
@[simp]
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl
@[simp]
theorem mem_attach (s : Finset α) : ∀ x, x ∈ s.attach :=
  Multiset.mem_attach _
end Finset