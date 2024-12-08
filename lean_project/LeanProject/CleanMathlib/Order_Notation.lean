import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Simps.NotationClass
@[notation_class]
class HasCompl (α : Type*) where
  compl : α → α
export HasCompl (compl)
@[inherit_doc]
postfix:1024 "ᶜ" => compl
@[deprecated Max (since := "2024-11-06"), notation_class, ext]
class Sup (α : Type*) where
  sup : α → α → α
@[deprecated Min (since := "2024-11-06"), notation_class, ext]
class Inf (α : Type*) where
  inf : α → α → α
attribute [ext] Min Max
@[inherit_doc]
infixl:68 " ⊔ " => Max.max
@[inherit_doc]
infixl:69 " ⊓ " => Min.min
@[notation_class]
class HImp (α : Type*) where
  himp : α → α → α
@[notation_class]
class HNot (α : Type*) where
  hnot : α → α
export HImp (himp)
export SDiff (sdiff)
export HNot (hnot)
infixr:60 " ⇨ " => himp
prefix:72 "￢" => hnot
@[notation_class, ext]
class Top (α : Type*) where
  top : α
@[notation_class, ext]
class Bot (α : Type*) where
  bot : α
notation "⊤" => Top.top
notation "⊥" => Bot.bot
instance (priority := 100) top_nonempty (α : Type*) [Top α] : Nonempty α :=
  ⟨⊤⟩
instance (priority := 100) bot_nonempty (α : Type*) [Bot α] : Nonempty α :=
  ⟨⊥⟩
attribute [match_pattern] Bot.bot Top.top