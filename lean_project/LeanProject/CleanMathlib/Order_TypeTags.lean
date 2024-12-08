import Mathlib.Order.Notation
variable {α : Type*}
def WithBot (α : Type*) := Option α
namespace WithBot
instance [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩
@[coe, match_pattern] def some : α → WithBot α :=
  Option.some
instance coe : Coe α (WithBot α) :=
  ⟨some⟩
instance bot : Bot (WithBot α) :=
  ⟨none⟩
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a
@[simp]
theorem recBotCoe_bot {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl
@[simp]
theorem recBotCoe_coe {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl
end WithBot
def WithTop (α : Type*) :=
  Option α
namespace WithTop
instance [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩
@[coe, match_pattern] def some : α → WithTop α :=
  Option.some
instance coeTC : CoeTC α (WithTop α) :=
  ⟨some⟩
instance top : Top (WithTop α) :=
  ⟨none⟩
instance inhabited : Inhabited (WithTop α) :=
  ⟨⊤⟩
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recTopCoe {C : WithTop α → Sort*} (top : C ⊤) (coe : ∀ a : α, C a) : ∀ n : WithTop α, C n
  | none => top
  | Option.some a => coe a
@[simp]
theorem recTopCoe_top {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) :
    @recTopCoe _ C d f ⊤ = d :=
  rfl
@[simp]
theorem recTopCoe_coe {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) (x : α) :
    @recTopCoe _ C d f ↑x = f x :=
  rfl
end WithTop