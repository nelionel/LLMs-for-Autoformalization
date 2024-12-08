import Mathlib.Tactic.FBinop
universe u v w
class SProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  sprod : α → β → γ
@[inherit_doc SProd.sprod] infixr:82 " ×ˢ " => SProd.sprod
macro_rules | `($x ×ˢ $y)   => `(fbinop% SProd.sprod $x $y)