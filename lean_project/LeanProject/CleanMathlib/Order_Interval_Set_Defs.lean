import Mathlib.Data.Set.Defs
import Mathlib.Order.Defs.PartialOrder
namespace Set
variable {α : Type*} [Preorder α] {a b x : α}
def Ioo (a b : α) := { x | a < x ∧ x < b }
@[simp] theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := Iff.rfl
theorem Ioo_def (a b : α) : { x | a < x ∧ x < b } = Ioo a b := rfl
def Ico (a b : α) := { x | a ≤ x ∧ x < b }
@[simp] theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := Iff.rfl
theorem Ico_def (a b : α) : { x | a ≤ x ∧ x < b } = Ico a b := rfl
def Iio (b : α) := { x | x < b }
@[simp] theorem mem_Iio : x ∈ Iio b ↔ x < b := Iff.rfl
theorem Iio_def (a : α) : { x | x < a } = Iio a := rfl
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }
@[simp] theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl
theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = Icc a b := rfl
def Iic (b : α) := { x | x ≤ b }
@[simp] theorem mem_Iic : x ∈ Iic b ↔ x ≤ b := Iff.rfl
theorem Iic_def (b : α) : { x | x ≤ b } = Iic b := rfl
def Ioc (a b : α) := { x | a < x ∧ x ≤ b }
@[simp] theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := Iff.rfl
theorem Ioc_def (a b : α) : { x | a < x ∧ x ≤ b } = Ioc a b := rfl
def Ici (a : α) := { x | a ≤ x }
@[simp] theorem mem_Ici : x ∈ Ici a ↔ a ≤ x := Iff.rfl
theorem Ici_def (a : α) : { x | a ≤ x } = Ici a := rfl
def Ioi (a : α) := { x | a < x }
@[simp] theorem mem_Ioi : x ∈ Ioi a ↔ a < x := Iff.rfl
theorem Ioi_def (a : α) : { x | a < x } = Ioi a := rfl
class OrdConnected (s : Set α) : Prop where
  out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s
end Set