import Batteries.Data.MLList.Basic
import Mathlib.Control.Combinators
import Std.Data.HashSet.Basic
set_option linter.deprecated false
universe u
variable {α : Type u} {m : Type u → Type u}
section
variable [Monad m] [Alternative m]
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def depthFirst' (f : Nat → α → m α) (n : Nat) (a : α) : m α :=
pure a <|> joinM ((f n a) <&> (depthFirst' f (n+1)))
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def depthFirst (f : α → m α) (a : α) (maxDepth : Option Nat := none) : m α :=
  match maxDepth with
  | some d => depthFirst' (fun n a => if n ≤ d then f a else failure) 0 a
  | none => depthFirst' (fun _ a => f a) 0 a
end
variable [Monad m]
open Lean in
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def depthFirstRemovingDuplicates {α : Type u} [BEq α] [Hashable α]
    (f : α → MLList m α) (a : α) (maxDepth : Option Nat := none) : MLList m α :=
let f' : α → MLList (StateT.{u} (Std.HashSet α) m) α := fun a =>
  (f a).liftM >>= fun b => do
    let s ← get
    if s.contains b then failure
    set <| s.insert b
    pure b
(depthFirst f' a maxDepth).runState' (Std.HashSet.empty.insert a)
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def depthFirstRemovingDuplicates' [BEq α] [Hashable α]
    (f : α → List α) (a : α) (maxDepth : Option Nat := none) : List α :=
depthFirstRemovingDuplicates
  (fun a => (.ofList (f a) : MLList Option α)) a maxDepth |>.force |>.get!