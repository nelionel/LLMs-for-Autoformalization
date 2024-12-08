import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header
open Lean Elab
namespace Mathlib.Linter
register_option linter.style.multiGoal : Bool := {
  defValue := false
  descr := "enable the multiGoal linter"
}
namespace Style.multiGoal
abbrev exclusions : Std.HashSet SyntaxNodeKind := .ofList [
    ``Lean.Parser.Term.cdot,
    ``cdot,
    ``cdotTk,
    ``Lean.Parser.Tactic.tacticSeqBracketed,
    `«;»,
    `«<;>»,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    `«{»,
    `«]»,
    `null,
    `then,
    `else,
    ``Lean.Parser.Tactic.«tacticNext_=>_»,
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    `Batteries.Tactic.tacticSwap,
    ``Lean.Parser.Tactic.rotateLeft,
    ``Lean.Parser.Tactic.rotateRight,
    ``Lean.Parser.Tactic.skip,
    `Batteries.Tactic.«tacticOn_goal-_=>_»,
    `Mathlib.Tactic.«tacticSwap_var__,,»,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticTry_,
    ``Lean.Parser.Tactic.paren,
    ``Lean.Parser.Tactic.case,
    ``Lean.Parser.Tactic.constructor,
    `Mathlib.Tactic.tacticAssumption',
    ``Lean.Parser.Tactic.induction,
    ``Lean.Parser.Tactic.cases,
    ``Lean.Parser.Tactic.intros,
    ``Lean.Parser.Tactic.injections,
    ``Lean.Parser.Tactic.substVars,
    `Batteries.Tactic.«tacticPick_goal-_»,
    ``Lean.Parser.Tactic.case',
    `«tactic#adaptation_note_»,
    `tacticSleep_heartbeats_
  ]
abbrev ignoreBranch : Std.HashSet SyntaxNodeKind := .ofList [
    ``Lean.Parser.Tactic.Conv.conv,
    `Mathlib.Tactic.Conv.convLHS,
    `Mathlib.Tactic.Conv.convRHS,
    ``Lean.Parser.Tactic.first,
    ``Lean.Parser.Tactic.repeat',
    ``Lean.Parser.Tactic.tacticIterate____,
    ``Lean.Parser.Tactic.anyGoals,
    ``Lean.Parser.Tactic.allGoals,
    ``Lean.Parser.Tactic.focus,
    ``Lean.Parser.Tactic.failIfSuccess,
    `Mathlib.Tactic.successIfFailWithMsg
  ]
partial
def getManyGoals : InfoTree → Array (Syntax × Nat × Nat × Nat)
  | .node info args =>
    let kargs := (args.map getManyGoals).toArray.flatten
    if let .ofTacticInfo info := info then
      if ignoreBranch.contains info.stx.getKind then #[]
      else if info.goalsBefore.length == 1 && info.goalsAfter.length ≤ 1 then kargs
      else if let .original .. := info.stx.getHeadInfo then
        let backgroundGoals := info.goalsAfter.filter (info.goalsBefore.contains ·)
        if backgroundGoals.length != 0 && !exclusions.contains info.stx.getKind then
          kargs.push (info.stx,
                      info.goalsBefore.length, info.goalsAfter.length, backgroundGoals.length)
        else kargs
      else kargs
    else kargs
  | .context _ t => getManyGoals t
  | _ => default
@[inherit_doc Mathlib.Linter.linter.style.multiGoal]
def multiGoalLinter : Linter where run := withSetOptionIn fun _stx ↦ do
    unless Linter.getLinterValue linter.style.multiGoal (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    let trees ← getInfoTrees
    for t in trees.toArray do
      for (s, before, after, n) in getManyGoals t do
        let goals (k : Nat) := if k == 1 then f!"1 goal" else f!"{k} goals"
        let fmt ← Command.liftCoreM
          try PrettyPrinter.ppTactic ⟨s⟩ catch _ => pure f!"(failed to pretty print)"
        Linter.logLint linter.style.multiGoal s m!"\
          The following tactic starts with {goals before} and ends with {goals after}, \
          {n} of which {if n == 1 then "is" else "are"} not operated on.\
          {indentD fmt}\n\
          Please focus on the current goal, for instance using `·` (typed as \"\\.\")."
initialize addLinter multiGoalLinter
end Style.multiGoal
end Mathlib.Linter