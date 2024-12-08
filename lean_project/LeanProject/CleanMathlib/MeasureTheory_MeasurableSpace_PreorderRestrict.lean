import Mathlib.Order.Restriction
import Mathlib.MeasureTheory.MeasurableSpace.Basic
open MeasureTheory
namespace Preorder
variable {α : Type*} [Preorder α] {X : α → Type*} [∀ a, MeasurableSpace (X a)]
@[measurability, fun_prop]
theorem measurable_restrictLe (a : α) : Measurable (restrictLe (π := X) a) :=
    Set.measurable_restrict _
@[measurability, fun_prop]
theorem measurable_restrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (restrictLe₂ (π := X) hab) :=
  Set.measurable_restrict₂ _
variable [LocallyFiniteOrderBot α]
@[measurability, fun_prop]
theorem measurable_frestrictLe (a : α) : Measurable (frestrictLe (π := X) a) :=
  Finset.measurable_restrict _
@[measurability, fun_prop]
theorem measurable_frestrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (frestrictLe₂ (π := X) hab) :=
  Finset.measurable_restrict₂ _
end Preorder