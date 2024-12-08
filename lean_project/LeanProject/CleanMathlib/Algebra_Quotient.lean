import Mathlib.Tactic.Common
universe u v
class HasQuotient (A : outParam <| Type u) (B : Type v) where
  quotient' : B → Type max u v
abbrev HasQuotient.Quotient (A : outParam <| Type u) {B : Type v}
    [HasQuotient A B] (b : B) : Type max u v :=
  HasQuotient.quotient' b
notation:35 G " ⧸ " H:34 => HasQuotient.Quotient G H