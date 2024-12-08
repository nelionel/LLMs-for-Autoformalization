import Mathlib.Data.Set.Defs
import Mathlib.Tactic.TypeStar
variable {α : Type*} [LE α]
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }
def lowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty
def BddBelow (s : Set α) :=
  (lowerBounds s).Nonempty
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s
def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)
def IsGLB (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
def IsCofinal (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, x ≤ y