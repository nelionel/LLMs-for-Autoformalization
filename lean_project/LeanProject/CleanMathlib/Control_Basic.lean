import Mathlib.Control.Combinators
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Attr.Core
universe u v w
variable {α β γ : Type u}
section Functor
attribute [functor_norm] Functor.map_map
end Functor
section Applicative
variable {F : Type u → Type v} [Applicative F]
def zipWithM {α₁ α₂ φ : Type u} (f : α₁ → α₂ → F φ) : ∀ (_ : List α₁) (_ : List α₂), F (List φ)
  | x :: xs, y :: ys => (· :: ·) <$> f x y <*> zipWithM f xs ys
  | _, _ => pure []
def zipWithM' (f : α → β → F γ) : List α → List β → F PUnit
  | x :: xs, y :: ys => f x y *> zipWithM' f xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit
variable [LawfulApplicative F]
@[simp]
theorem pure_id'_seq (x : F α) : (pure fun x => x) <*> x = x :=
  pure_id_seq x
@[functor_norm]
theorem seq_map_assoc (x : F (α → β)) (f : γ → α) (y : F γ) :
    x <*> f <$> y = (· ∘ f) <$> x <*> y := by
  simp only [← pure_seq]
  simp only [seq_assoc, Function.comp, seq_pure, ← comp_map]
  simp [pure_seq]
  rfl
@[functor_norm]
theorem map_seq (f : β → γ) (x : F (α → β)) (y : F α) :
    f <$> (x <*> y) = (f ∘ ·) <$> x <*> y := by
  simp only [← pure_seq]; simp [seq_assoc]
end Applicative
section Monad
variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
theorem seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} :
    f <$> x >>= g = x >>= g ∘ f :=
  show bind (f <$> x) g = bind x (g ∘ f) by
    rw [← bind_pure_comp, bind_assoc]
    simp [pure_bind, Function.comp_def]
@[functor_norm]
theorem fish_pure {α β} (f : α → m β) : f >=> pure = f := by
  simp (config := { unfoldPartialApp := true }) only [(· >=> ·), functor_norm]
@[functor_norm]
theorem fish_pipe {α β} (f : α → m β) : pure >=> f = f := by
  simp (config := { unfoldPartialApp := true }) only [(· >=> ·), functor_norm]
@[functor_norm]
theorem fish_assoc {α β γ φ} (f : α → m β) (g : β → m γ) (h : γ → m φ) :
    (f >=> g) >=> h = f >=> g >=> h := by
  simp (config := { unfoldPartialApp := true }) only [(· >=> ·), functor_norm]
variable {β' γ' : Type v}
variable {m' : Type v → Type w} [Monad m']
def List.mapAccumRM (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mapAccumRM f a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)
def List.mapAccumLM (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mapAccumLM f a' xs
    pure (a'', y :: ys)
end Monad
section
variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
theorem joinM_map_map {α β : Type u} (f : α → β) (a : m (m α)) :
    joinM (Functor.map f <$> a) = f <$> joinM a := by
  simp only [joinM, (· ∘ ·), id, ← bind_pure_comp, bind_assoc, map_bind, pure_bind]
theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joinM (joinM a) := by
  simp only [joinM, (· ∘ ·), id, map_bind, ← bind_pure_comp, bind_assoc, pure_bind]
@[simp]
theorem joinM_map_pure {α : Type u} (a : m α) : joinM (pure <$> a) = a := by
  simp only [joinM, (· ∘ ·), id, map_bind, ← bind_pure_comp, bind_assoc, pure_bind, bind_pure]
@[simp]
theorem joinM_pure {α : Type u} (a : m α) : joinM (pure a) = a :=
  LawfulMonad.pure_bind a id
end
section Alternative
variable {F : Type → Type v} [Alternative F]
def succeeds {α} (x : F α) : F Bool :=
  Functor.mapConst true x <|> pure false
def tryM {α} (x : F α) : F Unit :=
  Functor.mapConst () x <|> pure ()
def try? {α} (x : F α) : F (Option α) :=
  some <$> x <|> pure none
@[simp]
theorem guard_true {h : Decidable True} : @guard F _ True h = pure () := by simp [guard, if_pos]
@[simp]
theorem guard_false {h : Decidable False} : @guard F _ False h = failure := by
  simp [guard, if_neg not_false]
end Alternative
namespace Sum
variable {e : Type v}
protected def bind {α β} : e ⊕ α → (α → e ⊕ β) → e ⊕ β
  | inl x, _ => inl x
  | inr x, f => f x
instance : Monad (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bind e
instance : LawfulFunctor (Sum.{v, u} e) := by
  constructor <;> intros <;> (try casesm Sum _ _) <;> rfl
instance : LawfulMonad (Sum.{v, u} e) where
  seqRight_eq := by
    intros
    casesm Sum _ _ <;> casesm Sum _ _ <;> rfl
  seqLeft_eq := by
    intros
    casesm Sum _ _ <;> rfl
  pure_seq := by
    intros
    rfl
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map := by
    intros
    casesm Sum _ _ <;> rfl
end Sum
class CommApplicative (m : Type u → Type v) [Applicative m] extends LawfulApplicative m : Prop where
  commutative_prod : ∀ {α β} (a : m α) (b : m β),
    Prod.mk <$> a <*> b = (fun (b : β) a => (a, b)) <$> b <*> a
open Functor
theorem CommApplicative.commutative_map {m : Type u → Type v} [h : Applicative m]
    [CommApplicative m] {α β γ} (a : m α) (b : m β) {f : α → β → γ} :
  f <$> a <*> b = flip f <$> b <*> a :=
  calc
    f <$> a <*> b = (fun p : α × β => f p.1 p.2) <$> (Prod.mk <$> a <*> b) := by
      simp only [map_seq, map_map, Function.comp_def]
    _ = (fun b a => f a b) <$> b <*> a := by
      rw [@CommApplicative.commutative_prod m h]
      simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map, (· ∘ ·)]
      rfl