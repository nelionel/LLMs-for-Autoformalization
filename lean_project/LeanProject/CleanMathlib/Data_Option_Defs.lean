import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
namespace Option
protected def traverse.{u, v}
    {F : Type u → Type v} [Applicative F] {α : Type*} {β : Type u} (f : α → F β) :
    Option α → F (Option β)
  | none => pure none
  | some x => some <$> f x
variable {α : Type*} {β : Type*}
protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b
@[simp]
theorem elim'_none (b : β) (f : α → β) : Option.elim' b f none = b := rfl
@[simp]
theorem elim'_some {a : α} (b : β) (f : α → β) : Option.elim' b f (some a) = f a := rfl
lemma elim'_eq_elim {α β : Type*} (b : β) (f : α → β) (a : Option α) :
    Option.elim' b f a = Option.elim a b f := by
  cases a <;> rfl
theorem mem_some_iff {α : Type*} {a b : α} : a ∈ some b ↔ b = a := by simp
@[inline]
def decidableEqNone {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff isNone_iff_eq_none
instance decidableForallMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∀ a ∈ o, p a)
  | none => isTrue (by simp [false_imp_iff])
  | some a =>
      if h : p a then isTrue fun _ e ↦ some_inj.1 e ▸ h
      else isFalse <| mt (fun H ↦ H _ rfl) h
instance decidableExistsMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none => isFalse fun ⟨a, ⟨h, _⟩⟩ ↦ by cases h
  | some a => if h : p a then isTrue <| ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ ↦ h hn
abbrev iget [Inhabited α] : Option α → α
  | some x => x
  | none => default
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl
instance liftOrGet_isCommutative (f : α → α → α) [Std.Commutative f] :
    Std.Commutative (liftOrGet f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [liftOrGet, Std.Commutative.comm]⟩
instance liftOrGet_isAssociative (f : α → α → α) [Std.Associative f] :
    Std.Associative (liftOrGet f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [liftOrGet, Std.Associative.assoc]⟩
instance liftOrGet_isIdempotent (f : α → α → α) [Std.IdempotentOp f] :
    Std.IdempotentOp (liftOrGet f) :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet, Std.IdempotentOp.idempotent]⟩
instance liftOrGet_isId (f : α → α → α) : Std.LawfulIdentity (liftOrGet f) none where
  left_id a := by cases a <;> simp [liftOrGet]
  right_id a := by cases a <;> simp [liftOrGet]
def _root_.Lean.LOption.toOption {α} : Lean.LOption α → Option α
  | .some a => some a
  | _ => none
end Option