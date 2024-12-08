import Mathlib.Data.Fintype.Powerset
variable {α : Type*}
namespace Finite
instance [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance
end Finite