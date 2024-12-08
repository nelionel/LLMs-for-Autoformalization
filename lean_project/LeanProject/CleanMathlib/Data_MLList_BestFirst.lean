import Batteries.Data.MLList.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.Estimator
open Batteries EstimatorData Estimator Set
section
structure BestFirstNode {α : Sort*} {ω : Type*} (prio : α → Thunk ω) (ε : α → Type) where
  key : α
  estimator : ε key
variable {ω α : Type} {prio : α → Thunk ω} {ε : α → Type} [LinearOrder ω]
  [∀ a, Estimator (prio a) (ε a)]
  [I : ∀ a : α, WellFoundedGT (range (bound (prio a) : ε a → ω))]
  {m : Type → Type} [Monad m] {β : Type}
def BestFirstNode.estimate (n : BestFirstNode prio ε) : ω := bound (prio n.key) n.estimator
instance [Ord ω] [Ord α] : Ord (BestFirstNode prio ε) where
  compare :=
    compareLex
      (compareOn BestFirstNode.estimate)
      (compareOn BestFirstNode.key)
set_option linter.unusedVariables false in
variable (prio ε m β) [Ord ω] [Ord α] in
@[nolint unusedArguments]
def BestFirstQueue (maxSize : Option Nat) := RBMap (BestFirstNode prio ε) (MLList m β) compare
variable [Ord ω] [Ord α] {maxSize : Option Nat}
namespace BestFirstQueue
def insertAndEject
    (q : BestFirstQueue prio ε m β maxSize) (n : BestFirstNode prio ε) (l : MLList m β) :
    BestFirstQueue prio ε m β maxSize :=
  match maxSize with
  | none => q.insert n l
  | some max =>
    if q.size < max then
      q.insert n l
    else
      match q.max? with
      | none => RBMap.empty
      | some m => q.insert n l |>.erase m.1
partial def ensureFirstIsBest (q : BestFirstQueue prio ε m β maxSize) :
    m (BestFirstQueue prio ε m β maxSize) := do
  let s := @toStream (RBMap _ _ _) _ _ q
  match s.next? with
  | none =>
    return q
  | some ((n, l), s') => match s'.next? with
    | none => do
      return q
    | some ((m, _), _) =>
      match improveUntil (prio n.key) (m.estimate < ·) n.estimator with
      | .error none =>
        return q
      | .error (some e') =>
        return q.erase n |>.insert ⟨n.key, e'⟩ l
      | .ok e' =>
        ensureFirstIsBest (q.erase n |>.insert ⟨n.key, e'⟩ l)
partial def popWithBound (q : BestFirstQueue prio ε m β maxSize) :
    m (Option (((a : α) × (ε a) × β) × BestFirstQueue prio ε m β maxSize)) := do
  let q' ← ensureFirstIsBest q
  match q'.min? with
  | none =>
    return none
  | some (n, l) =>
    match ← l.uncons with
    | none =>
      popWithBound (q'.erase n)
    | some (b, l') =>
      return some (⟨n.key, n.estimator, b⟩, q'.modify n fun _ => l')
def popWithPriority (q : BestFirstQueue prio ε m β maxSize) :
    m (Option (((α × ω) × β) × BestFirstQueue prio ε m β maxSize)) := do
  match ← q.popWithBound with
  | none => pure none
  | some (⟨a, e, b⟩, q') => pure (some (((a, bound (prio a) e), b), q'))
def pop (q : BestFirstQueue prio ε m β maxSize) :
    m (Option ((α × β) × BestFirstQueue prio ε m β maxSize)) := do
  match ← q.popWithBound with
  | none => pure none
  | some (⟨a, _, b⟩, q') => pure (some ((a, b), q'))
partial def toMLListWithPriority (q : BestFirstQueue prio ε m β maxSize) : MLList m ((α × ω) × β) :=
  .squash fun _ => do
    match ← q.popWithPriority with
    | none => pure .nil
    | some (p, q') => pure <| MLList.cons p q'.toMLListWithPriority
def toMLList (q : BestFirstQueue prio ε m β maxSize) : MLList m (α × β) :=
  q.toMLListWithPriority.map fun t => (t.1.1, t.2)
end BestFirstQueue
open MLList
variable {m : Type → Type} [Monad m] [Alternative m] [∀ a, Bot (ε a)] (prio ε)
def impl (maxSize : Option Nat) (f : α → MLList m α) (a : α) : MLList m α :=
  let init : BestFirstQueue prio ε m α maxSize := RBMap.single ⟨a, ⊥⟩ (f a)
  cons a (iterate go |>.runState' init)
where
  go : StateT (BestFirstQueue prio ε m α maxSize) m α := fun s => do
  match ← s.pop with
    | none => failure
    | some ((_, b), s') => pure (b, s'.insertAndEject ⟨b, ⊥⟩ (f b))
def implMaxDepth (maxSize : Option Nat) (maxDepth : Option Nat) (f : α → MLList m α) (a : α) :
    MLList m α :=
  match maxDepth with
  | none => impl prio ε maxSize f a
  | some max =>
    let f' : α ×ₗ Nat → MLList m (α × Nat) := fun ⟨a, n⟩ =>
      if max < n then
        nil
      else
        (f a).map fun a' => (a', n + 1)
    impl (fun p : α ×ₗ Nat => prio p.1) (fun p : α ×ₗ Nat => ε p.1) maxSize f' (a, 0) |>.map (·.1)
def bestFirstSearchCore (f : α → MLList m α) (a : α)
    (β : Type _) [Ord β] (removeDuplicatesBy? : Option (α → β) := none)
    (maxQueued : Option Nat := none) (maxDepth : Option Nat := none)  :
    MLList m α :=
  match removeDuplicatesBy? with
  | some g =>
    let f' : α → MLList (StateT (RBSet β compare) m) α := fun a =>
      (f a).liftM >>= fun a' => do
        let b := g a'
        guard !(← get).contains b
        modify fun s => s.insert b
        pure a'
    implMaxDepth prio ε maxQueued maxDepth f' a |>.runState' (RBSet.empty.insert (g a))
  | none =>
    implMaxDepth prio ε maxQueued maxDepth f a
end
variable {m : Type → Type} {α : Type} [Monad m] [Alternative m] [LinearOrder α]
local instance instOrderBotEq {a : α} : OrderBot { x : α // x = a } where
  bot := ⟨a, rfl⟩
  bot_le := by aesop
def bestFirstSearch (f : α → MLList m α) (a : α)
    (maxQueued : Option Nat := none) (maxDepth : Option Nat := none) (removeDuplicates := true) :
    MLList m α :=
  bestFirstSearchCore Thunk.pure (fun a : α => { x // x = a }) f a
    (β := α) (removeDuplicatesBy? := if removeDuplicates then some id else none)
    maxQueued maxDepth