import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ToAdditive
class PosPart (α : Type*) where
  posPart : α → α
@[to_additive]
class OneLePart (α : Type*) where
  oneLePart : α → α
class NegPart (α : Type*) where
  negPart : α → α
@[to_additive]
class LeOnePart (α : Type*) where
  leOnePart : α → α
export OneLePart (oneLePart)
export LeOnePart (leOnePart)
export PosPart (posPart)
export NegPart (negPart)
@[inherit_doc] postfix:max "⁺ᵐ " => OneLePart.oneLePart
@[inherit_doc] postfix:max "⁻ᵐ" => LeOnePart.leOnePart
@[inherit_doc] postfix:max "⁺" => PosPart.posPart
@[inherit_doc] postfix:max "⁻" => NegPart.negPart