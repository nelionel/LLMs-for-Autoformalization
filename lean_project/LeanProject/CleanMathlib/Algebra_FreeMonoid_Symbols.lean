import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
variable {α : Type*} [DecidableEq α]
namespace FreeMonoid
@[to_additive "The set of unique symbols in an additive free monoid element"]
def symbols (a : FreeMonoid α) : Finset α := List.toFinset a
@[to_additive (attr := simp)]
theorem symbols_one : symbols (1 : FreeMonoid α) = ∅ := rfl
@[to_additive (attr := simp)]
theorem symbols_of {m : α} : symbols (of m) = {m} := rfl
@[to_additive (attr := simp)]
theorem symbols_mul {a b : FreeMonoid α} : symbols (a * b) = symbols a ∪ symbols b := by
  simp only [symbols, List.mem_toFinset, Finset.mem_union]
  apply List.toFinset_append
@[to_additive (attr := simp)]
theorem mem_symbols {m : α} {a : FreeMonoid α} : m ∈ symbols a ↔ m ∈ a :=
  List.mem_toFinset
end FreeMonoid