import Mathlib.Data.Nat.Notation
universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}
def Stream' (α : Type u) := ℕ → α
namespace Stream'
def cons (a : α) (s : Stream' α) : Stream' α
  | 0 => a
  | n + 1 => s n
scoped infixr:67 " :: " => cons
def get (s : Stream' α) (n : ℕ) : α := s n
abbrev head (s : Stream' α) : α := s.get 0
def tail (s : Stream' α) : Stream' α := fun i => s.get (i + 1)
def drop (n : ℕ) (s : Stream' α) : Stream' α := fun i => s.get (i + n)
def All (p : α → Prop) (s : Stream' α) := ∀ n, p (get s n)
def Any (p : α → Prop) (s : Stream' α) := ∃ n, p (get s n)
instance : Membership α (Stream' α) :=
  ⟨fun s a => Any (fun b => a = b) s⟩
def map (f : α → β) (s : Stream' α) : Stream' β := fun n => f (get s n)
def zip (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ :=
  fun n => f (get s₁ n) (get s₂ n)
def enum (s : Stream' α) : Stream' (ℕ × α) := fun n => (n, s.get n)
def const (a : α) : Stream' α := fun _ => a
def iterate (f : α → α) (a : α) : Stream' α
  | 0 => a
  | n + 1 => f (iterate f a n)
def corec (f : α → β) (g : α → α) : α → Stream' β := fun a => map f (iterate g a)
def corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a
def corec' (f : α → β × α) : α → Stream' β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)
abbrev unfolds (g : α → β) (f : α → α) (a : α) : Stream' β :=
  corec g f a
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)
infixl:65 " ⋈ " => interleave
def even (s : Stream' α) : Stream' α :=
  corec head (fun s => tail (tail s)) s
def odd (s : Stream' α) : Stream' α :=
  even (tail s)
def appendStream' : List α → Stream' α → Stream' α
  | [], s => s
  | List.cons a l, s => a::appendStream' l s
infixl:65 " ++ₛ " => appendStream'
def take : ℕ → Stream' α → List α
  | 0, _ => []
  | n + 1, s => List.cons (head s) (take n (tail s))
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)
def cycle : ∀ l : List α, l ≠ [] → Stream' α
  | [], h => absurd rfl h
  | List.cons a l, _ => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)
def tails (s : Stream' α) : Stream' (Stream' α) :=
  corec id tail (tail s)
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [head s] (tail s)
def pure (a : α) : Stream' α :=
  const a
def apply (f : Stream' (α → β)) (s : Stream' α) : Stream' β := fun n => (get f n) (get s n)
infixl:75 " ⊛ " => apply
def nats : Stream' ℕ := fun n => n
end Stream'