import Mathlib.Algebra.Order.Field.Canonical.Defs
variable {α : Type*}
section CanonicallyLinearOrderedSemifield
variable [CanonicallyLinearOrderedSemifield α] [Sub α] [OrderedSub α]
theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
end CanonicallyLinearOrderedSemifield