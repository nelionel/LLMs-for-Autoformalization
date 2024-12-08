import Mathlib.Order.Basic
variable {α : Type*}
open Function
class ZeroLEOneClass (α : Type*) [Zero α] [One α] [LE α] : Prop where
  zero_le_one : (0 : α) ≤ 1
@[simp] lemma zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  ZeroLEOneClass.zero_le_one
lemma zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
section
variable [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]
@[simp] lemma zero_lt_one : (0 : α) < 1 := zero_le_one.lt_of_ne (NeZero.ne' 1)
variable (α)
lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one
end
alias one_pos := zero_lt_one