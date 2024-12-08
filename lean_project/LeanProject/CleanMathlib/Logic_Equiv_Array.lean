import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.List
namespace Equiv
def arrayEquivList (α : Type*) : Array α ≃ List α :=
  ⟨Array.toList, Array.mk, fun _ => rfl, fun _ => rfl⟩
end Equiv
instance Array.encodable {α} [Encodable α] : Encodable (Array α) :=
  Encodable.ofEquiv _ (Equiv.arrayEquivList _)
instance Array.countable {α} [Countable α] : Countable (Array α) :=
  Countable.of_equiv _ (Equiv.arrayEquivList α).symm