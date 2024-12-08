import Mathlib.Init
import Lean.Elab.Tactic.Basic
open Lean Elab
def sleepAtLeastHeartbeats (n : Nat) : IO Unit := do
  let i ← IO.getNumHeartbeats
  while (← IO.getNumHeartbeats) < i + n do
    continue
elab "sleep_heartbeats " n:num : tactic => do
  match Syntax.isNatLit? n with
  | none    => throwIllFormedSyntax
  | some m => sleepAtLeastHeartbeats (m * 1000)
example : 1 = 1 := by
  sleep_heartbeats 1000
  rfl