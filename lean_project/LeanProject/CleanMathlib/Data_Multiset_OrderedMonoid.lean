import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
variable {α : Type*}
namespace Multiset
open List
instance : OrderedCancelAddCommMonoid (Multiset α) where
  add_le_add_left := fun _ _ => add_le_add_left
  le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left
instance : CanonicallyOrderedAddCommMonoid (Multiset α) where
  __ := inferInstanceAs (OrderBot (Multiset α))
  le_self_add := le_add_right
  exists_add_of_le h := exists_add_of_le h
end Multiset