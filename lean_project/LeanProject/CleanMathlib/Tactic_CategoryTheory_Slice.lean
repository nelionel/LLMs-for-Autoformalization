import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Conv
open CategoryTheory
open Lean Parser.Tactic Elab Command Elab.Tactic Meta
open Tactic
open Parser.Tactic.Conv
syntax (name := slice) "slice " num ppSpace num : conv
def evalSlice (a b : Nat) : TacticM Unit := do
  let _ ← iterateUntilFailureWithResults do
    evalTactic (← `(conv| rw [Category.assoc]))
  iterateRange (a - 1) (a - 1) do
      evalTactic (← `(conv| congr))
      evalTactic (← `(tactic| rotate_left))
  let k ← iterateUntilFailureCount
    <| evalTactic (← `(conv| rw [← Category.assoc]))
  let c := k+1+a-b
  iterateRange c c <| evalTactic (← `(conv| congr))
  let _ ← iterateUntilFailureWithResults do
    evalTactic (← `(conv| rw [Category.assoc]))
elab "slice " a:num ppSpace b:num : conv => evalSlice a.getNat b.getNat
syntax (name := sliceLHS) "slice_lhs " num ppSpace num " => " convSeq : tactic
macro_rules
  | `(tactic| slice_lhs $a $b => $seq) =>
    `(tactic| conv => lhs; slice $a $b; ($seq:convSeq))
syntax (name := sliceRHS) "slice_rhs " num ppSpace num " => " convSeq : tactic
macro_rules
  | `(tactic| slice_rhs $a $b => $seq) =>
    `(tactic| conv => rhs; slice $a $b; ($seq:convSeq))