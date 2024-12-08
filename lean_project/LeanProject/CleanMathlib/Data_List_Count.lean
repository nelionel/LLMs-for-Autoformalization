import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Common
assert_not_exists Set.range
assert_not_exists GroupWithZero
assert_not_exists Ring
open Nat
variable {α : Type*}
namespace List
section Count
@[simp]
theorem count_map_of_injective {β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countP_map]
  unfold Function.comp
  simp only [hf.beq_eq]
end Count
end List