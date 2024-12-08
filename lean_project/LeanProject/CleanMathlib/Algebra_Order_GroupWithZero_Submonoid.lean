import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Order.Interval.Set.Defs
namespace Submonoid
variable (α) [MulZeroOneClass α] [PartialOrder α] [PosMulStrictMono α] [ZeroLEOneClass α]
  [NeZero (1 : α)] {a : α}
@[simps] def pos : Submonoid α where
  carrier := Set.Ioi 0
  one_mem' := zero_lt_one
  mul_mem' := mul_pos
variable {α}
@[simp] lemma mem_pos : a ∈ pos α ↔ 0 < a := Iff.rfl
end Submonoid