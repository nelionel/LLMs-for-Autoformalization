import Mathlib.Init
namespace Mathlib.Meta.FunProp
universe u v
inductive StateList (σ α : Type u) where
  | nil : StateList σ α
  | cons : α → σ → StateList σ α → StateList σ α
variable {α β σ : Type u}
namespace StateList
private def toList : StateList σ α → List (α × σ)
  | .cons a s l => (a, s) :: l.toList
  | .nil => []
private def toList' : StateList σ α → List α
  | .cons a _ l => a :: l.toList'
  | .nil => []
private def map (f : α → β) : StateList σ α → StateList σ β
  | .cons a s l   => .cons (f a) s (l.map f)
  | .nil => .nil
private def append : (xs ys : StateList σ α) → StateList σ α
  | .nil,         bs => bs
  | .cons a s l, bs => .cons a s (l.append bs)
instance : Append (StateList σ α) := ⟨StateList.append⟩
@[specialize]
private def foldrM {m} [Monad m] : (f : α → σ → β → m β) → (init : β) → StateList σ α → m β
  | _, b, .nil     => pure b
  | f, b, .cons a s l => do
    f a s (← l.foldrM f b)
end StateList
def StateListT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (StateList σ α)
variable {m : Type u → Type v} [Monad m]
@[always_inline, inline]
def StateListT.run [Functor m] (x : StateListT σ m α) (s : σ) : m (List (α × σ)) :=
  StateList.toList <$> x s
@[always_inline, inline]
def StateListT.run' [Functor m] (x : StateListT σ m α) (s : σ) : m (List α) :=
  StateList.toList' <$> x s
abbrev StateListM (σ α : Type u) : Type u := StateListT σ Id α
namespace StateListT
section
@[always_inline, inline]
private def pure (a : α) : StateListT σ m α :=
  fun s => return StateList.nil.cons a s
@[always_inline, inline]
private def bind (x : StateListT σ m α) (f : α → StateListT σ m β) : StateListT σ m β :=
  fun s => do match ← x s with
    | .nil => return .nil
    | .cons a s .nil => f a s
    | x => x.foldrM (fun a s bs => return (← f a s) ++ bs) .nil
@[always_inline, inline]
private def map (f : α → β) (x : StateListT σ m α) : StateListT σ m β :=
  fun s => StateList.map f <$> x s
@[always_inline]
instance : Monad (StateListT σ m) where
  pure := StateListT.pure
  bind := StateListT.bind
  map  := StateListT.map
@[always_inline, inline]
private def orElse (x : StateListT σ m α) (y : Unit → StateListT σ m α) : StateListT σ m α :=
  fun s => (· ++ ·) <$> x s <*> y () s
@[always_inline, inline]
private def failure : StateListT σ m α :=
  fun _ => return .nil
instance : Alternative (StateListT σ m) where
  failure := StateListT.failure
  orElse  := StateListT.orElse
@[always_inline, inline]
protected def get : StateListT σ m σ :=
  fun s => return StateList.nil.cons s s
@[always_inline, inline]
protected def set : σ → StateListT σ m PUnit :=
  fun s' _ => return StateList.nil.cons ⟨⟩ s'
@[always_inline, inline]
protected def modifyGet (f : σ → α × σ) : StateListT σ m α :=
  fun s => let a := f s; return StateList.nil.cons a.1 a.2
@[always_inline, inline]
protected def lift (t : m α) : StateListT σ m α :=
  fun s => do let a ← t; return StateList.nil.cons a s
instance : MonadLift m (StateListT σ m) := ⟨StateListT.lift⟩
@[always_inline]
instance : MonadFunctor m (StateListT σ m) := ⟨fun f x s => f (x s)⟩
@[always_inline]
instance{ε} [MonadExceptOf ε m] : MonadExceptOf ε (StateListT σ m) := {
  throw    := StateListT.lift ∘ throwThe ε
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)
}
end
end StateListT
instance : MonadStateOf σ (StateListT σ m) where
  get       := StateListT.get
  set       := StateListT.set
  modifyGet := StateListT.modifyGet
@[always_inline]
instance StateListT.monadControl : MonadControl m (StateListT σ m) where
  stM      := StateList σ
  liftWith := fun f => do let s ← get; liftM (f (fun x => x s))
  restoreM := fun x _ => x
end Mathlib.Meta.FunProp