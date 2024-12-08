import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Vector
assert_not_exists OrderedRing
assert_not_exists MonoidWithZero
namespace List
variable (α : Type*) [Finite α] (n : ℕ)
lemma finite_length_eq : {l : List α | l.length = n}.Finite := Mathlib.Vector.finite
lemma finite_length_lt : {l : List α | l.length < n}.Finite := by
  convert (Finset.range n).finite_toSet.biUnion fun i _ ↦ finite_length_eq α i; ext; simp
lemma finite_length_le : {l : List α | l.length ≤ n}.Finite := by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)
end List