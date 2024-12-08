import Mathlib.Init
import Lean.Util.Heartbeats
import Lean.Meta.Tactic.TryThis
open Lean Elab Command Meta
namespace Mathlib.CountHeartbeats
open Tactic
def runTacForHeartbeats (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (revert : Bool := true) :
    TacticM Nat := do
  let start ← IO.getNumHeartbeats
  let s ← saveState
  evalTactic tac
  if revert then restoreState s
  return (← IO.getNumHeartbeats) - start
def variation (counts : List Nat) : List Nat :=
  let min := counts.min?.getD 0
  let max := counts.max?.getD 0
  let toFloat (n : Nat) := n.toUInt64.toFloat
  let toNat (f : Float) := f.toUInt64.toNat
  let counts' := counts.map toFloat
  let μ : Float := counts'.foldl (· + ·) 0 / toFloat counts.length
  let stddev : Float := Float.sqrt <|
    ((counts'.map fun i => (i - μ)^2).foldl (· + ·) 0) / toFloat counts.length
  [min, max, toNat stddev]
def logVariation {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (counts : List Nat) : m Unit := do
  if let [min, max, stddev] := variation counts then
  logInfo s!"Min: {min / 1000} Max: {max / 1000} StdDev: {stddev / 10}%"
elab "count_heartbeats " tac:tacticSeq : tactic => do
  logInfo s!"{← runTacForHeartbeats tac (revert := false)}"
elab "count_heartbeats! " n:(num)? "in" ppLine tac:tacticSeq : tactic => do
  let n := match n with
           | some j => j.getNat
           | none => 10
  let counts ← (List.range (n - 1)).mapM fun _ => runTacForHeartbeats tac
  let counts := (← runTacForHeartbeats tac (revert := false)) :: counts
  logVariation counts
elab "count_heartbeats " "in" ppLine cmd:command : command => do
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    let elapsed := (finish - start) / 1000
    let max := (← Command.liftCoreM getMaxHeartbeats) / 1000
    if elapsed < max then
      logInfo m!"Used {elapsed} heartbeats, which is less than the current maximum of {max}."
    else
      let mut max' := max
      while max' < elapsed do
        max' := 2 * max'
      logInfo m!"Used {elapsed} heartbeats, which is greater than the current maximum of {max}."
      let m : TSyntax `num := quote max'
      Command.liftCoreM <| MetaM.run' do
        Lean.Meta.Tactic.TryThis.addSuggestion (← getRef)
          (← set_option hygiene false in `(command| set_option maxHeartbeats $m in $cmd))
elab "guard_min_heartbeats " n:(num)? "in" ppLine cmd:command : command => do
  let max := (← Command.liftCoreM getMaxHeartbeats) / 1000
  let n := match n with
           | some j => j.getNat
           | none => max
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    let elapsed := (finish - start) / 1000
    if elapsed < n then
      logInfo m!"Used {elapsed} heartbeats, which is less than the minimum of {n}."
def elabForHeartbeats (cmd : TSyntax `command) (revert : Bool := true) : CommandElabM Nat := do
  let start ← IO.getNumHeartbeats
  let s ← get
  elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  if revert then set s
  return (← IO.getNumHeartbeats) - start
elab "count_heartbeats! " n:(num)? "in" ppLine cmd:command : command => do
  let n := match n with
           | some j => j.getNat
           | none => 10
  let counts ← (List.range (n - 1)).mapM fun _ => elabForHeartbeats cmd
  let counts := (← elabForHeartbeats cmd (revert := false)) :: counts
  logVariation counts
end CountHeartbeats
end Mathlib