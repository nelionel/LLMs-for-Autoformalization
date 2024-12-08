import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Basic
assert_not_exists OrderedAddCommMonoid
assert_not_exists Ring
open Function
open scoped Pointwise
variable {α : Type*}
namespace Set
section MulZeroClass
variable [MulZeroClass α] {s : Set α}
lemma mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
lemma zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]
lemma Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
lemma Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
end MulZeroClass
section GroupWithZero
variable [GroupWithZero α] {s : Set α}
lemma div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
lemma zero_div_subset (s : Set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]
lemma Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
lemma Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
end GroupWithZero
end Set