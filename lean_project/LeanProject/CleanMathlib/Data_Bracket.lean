import Mathlib.Tactic.TypeStar
class Bracket (L M : Type*) where
  bracket : L → M → M
@[inherit_doc] notation "⁅" x ", " y "⁆" => Bracket.bracket x y