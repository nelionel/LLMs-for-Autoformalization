import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Finite.Defs
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
universe u v
variable {α : Type u}
instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α (by rfl)
instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α (by rfl)
instance [h : Infinite α] : Infinite (Additive α) := h
instance [h : Infinite α] : Infinite (Multiplicative α) := h