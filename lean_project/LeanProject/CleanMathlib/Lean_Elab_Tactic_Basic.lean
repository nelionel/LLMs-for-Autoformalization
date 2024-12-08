import Mathlib.Lean.Meta
open Lean Elab Tactic
namespace Lean.Elab.Tactic
def getMainTarget'' : TacticM Expr := do
  (← getMainGoal).getType''
def doneWithScope (scope : MessageData) : TacticM Unit := do
  let gs ← getUnsolvedGoals
  unless gs.isEmpty do
    logError m!"{scope} failed to solve some goals.\n"
    Term.reportUnsolvedGoals gs
    throwAbortTactic
def focusAndDoneWithScope {α : Type} (scope : MessageData) (tactic : TacticM α) : TacticM α :=
  focus do
    let a ← try tactic catch e =>
      if isAbortTacticException e then throw e
      else throwError "{scope} failed.\n{← nestedExceptionToMessageData e}"
    doneWithScope scope
    pure a
end Lean.Elab.Tactic