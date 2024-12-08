import Mathlib.Data.Set.Operations
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.Hom.Basic
import Mathlib.Lean.Thunk
variable {α ε : Type*}
class EstimatorData (a : Thunk α) (ε : Type*) where
  bound : ε → α
  improve : ε → Option ε
class Estimator [Preorder α] (a : Thunk α) (ε : Type*) extends EstimatorData a ε where
  bound_le e : bound e ≤ a.get
  improve_spec e : match improve e with
    | none => bound e = a.get
    | some e' => bound e < bound e'
open EstimatorData Set
section trivial
variable [Preorder α]
abbrev Estimator.trivial.{u} {α : Type u} (a : α) : Type u := { b : α // b = a }
instance {a : α} : Bot (Estimator.trivial a) := ⟨⟨a, rfl⟩⟩
instance : WellFoundedGT Unit where
  wf := ⟨fun .unit => ⟨Unit.unit, nofun⟩⟩
instance (a : α) : WellFoundedGT (Estimator.trivial a) :=
  let f : Estimator.trivial a ≃o Unit := RelIso.relIsoOfUniqueOfRefl _ _
  let f' : Estimator.trivial a ↪o Unit := f.toOrderEmbedding
  f'.wellFoundedGT
instance {a : α} : Estimator (Thunk.pure a) (Estimator.trivial a) where
  bound b := b.val
  improve _ := none
  bound_le b := b.prop.le
  improve_spec b := b.prop
end trivial
section improveUntil
variable [Preorder α]
attribute [local instance] WellFoundedGT.toWellFoundedRelation in
def Estimator.improveUntilAux
    (a : Thunk α) (p : α → Bool) [Estimator a ε]
    [WellFoundedGT (range (bound a : ε → α))]
    (e : ε) (r : Bool) : Except (Option ε) ε :=
    if p (bound a e) then
      return e
    else
      match improve a e, improve_spec e with
      | none, _ => .error <| if r then none else e
      | some e', _ =>
        improveUntilAux a p e' true
termination_by (⟨_, mem_range_self e⟩ : range (bound a))
def Estimator.improveUntil (a : Thunk α) (p : α → Bool)
    [Estimator a ε] [WellFoundedGT (range (bound a : ε → α))] (e : ε) :
    Except (Option ε) ε :=
  Estimator.improveUntilAux a p e false
attribute [local instance] WellFoundedGT.toWellFoundedRelation in
theorem Estimator.improveUntilAux_spec (a : Thunk α) (p : α → Bool)
    [Estimator a ε] [WellFoundedGT (range (bound a : ε → α))] (e : ε) (r : Bool) :
    match Estimator.improveUntilAux a p e r with
    | .error _ => ¬ p a.get
    | .ok e' => p (bound a e') := by
  rw [Estimator.improveUntilAux]
  by_cases h : p (bound a e)
  · simp only [h]; exact h
  · simp only [h]
    match improve a e, improve_spec e with
    | none, eq =>
      simp only [Bool.not_eq_true]
      rw [eq] at h
      exact Bool.bool_eq_false h
    | some e', _ =>
      exact Estimator.improveUntilAux_spec a p e' true
termination_by (⟨_, mem_range_self e⟩ : range (bound a))
theorem Estimator.improveUntil_spec
    (a : Thunk α) (p : α → Bool) [Estimator a ε] [WellFoundedGT (range (bound a : ε → α))] (e : ε) :
    match Estimator.improveUntil a p e with
    | .error _ => ¬ p a.get
    | .ok e' => p (bound a e') :=
  Estimator.improveUntilAux_spec a p e false
end improveUntil
section add
variable [Preorder α]
@[simps]
instance [Add α] {a b : Thunk α} (εa εb : Type*) [EstimatorData a εa] [EstimatorData b εb] :
    EstimatorData (a + b) (εa × εb) where
  bound e := bound a e.1 + bound b e.2
  improve e := match improve a e.1 with
  | some e' => some { e with fst := e' }
  | none => match improve b e.2 with
    | some e' => some { e with snd := e' }
    | none => none
instance (a b : Thunk ℕ) {εa εb : Type*} [Estimator a εa] [Estimator b εb] :
    Estimator (a + b) (εa × εb) where
  bound_le e :=
    Nat.add_le_add (Estimator.bound_le e.1) (Estimator.bound_le e.2)
  improve_spec e := by
    dsimp
    have s₁ := Estimator.improve_spec (a := a) e.1
    have s₂ := Estimator.improve_spec (a := b) e.2
    revert s₁ s₂
    cases improve a e.fst <;> cases improve b e.snd <;> intro s₁ s₂ <;> simp_all only
    · apply Nat.add_lt_add_left s₂
    · apply Nat.add_lt_add_right s₁
    · apply Nat.add_lt_add_right s₁
end add
section fst
variable {β : Type*} [PartialOrder α] [PartialOrder β]
structure Estimator.fst
    (p : Thunk (α × β)) (ε : Type*) [Estimator p ε] where
  inner : ε
variable [∀ a : α, WellFoundedGT { x // x ≤ a }]
instance {a : Thunk α} [Estimator a ε] : WellFoundedGT (range (bound a : ε → α)) :=
  let f : range (bound a : ε → α) ↪o { x // x ≤ a.get } :=
    Subtype.orderEmbedding (by rintro _ ⟨e, rfl⟩; exact Estimator.bound_le e)
  f.wellFoundedGT
instance [DecidableRel ((· : α) < ·)] {a : Thunk α} {b : Thunk β}
    (ε : Type*) [Estimator (a.prod b) ε] [∀ (p : α × β), WellFoundedGT { q // q ≤ p }] :
    EstimatorData a (Estimator.fst (a.prod b) ε) where
  bound e := (bound (a.prod b) e.inner).1
  improve e :=
    let bd := (bound (a.prod b) e.inner).1
    Estimator.improveUntil (a.prod b) (fun p => bd < p.1) e.inner
      |>.toOption |>.map Estimator.fst.mk
def Estimator.fstInst [DecidableRel ((· : α) < ·)] [∀ (p : α × β), WellFoundedGT { q // q ≤ p }]
    (a : Thunk α) (b : Thunk β) (i : Estimator (a.prod b) ε) :
    Estimator a (Estimator.fst (a.prod b) ε) where
  bound_le e := (Estimator.bound_le e.inner : bound (a.prod b) e.inner ≤ (a.get, b.get)).1
  improve_spec e := by
    let bd := (bound (a.prod b) e.inner).1
    have := Estimator.improveUntil_spec (a.prod b) (fun p => bd < p.1) e.inner
    revert this
    simp only [EstimatorData.improve, decide_eq_true_eq]
    match Estimator.improveUntil (a.prod b) _ _ with
    | .error _ =>
      simp only [Option.map_none']
      exact fun w =>
        eq_of_le_of_not_lt
          (Estimator.bound_le e.inner : bound (a.prod b) e.inner ≤ (a.get, b.get)).1 w
    | .ok e' => exact fun w => w
end fst