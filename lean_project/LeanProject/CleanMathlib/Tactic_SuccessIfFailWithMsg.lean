import Lean.Elab.Eval
import Lean.Elab.Tactic.BuiltinTactic
import Mathlib.Init
open Lean Elab Tactic
namespace Mathlib.Tactic
syntax (name := successIfFailWithMsg) "success_if_fail_with_msg " term:max tacticSeq : tactic
def successIfFailWithMessage {s α : Type} {m : Type → Type}
    [Monad m] [MonadLiftT IO m] [MonadBacktrack s m] [MonadError m]
    (msg : String) (tacs : m α) (ref : Option Syntax := none) : m Unit := do
  let s ← saveState
  let err ←
    try _ ← tacs; pure none
    catch err => pure (some (← err.toMessageData.toString))
  restoreState s
  if let some err := err then
    unless msg.trim == err.trim do
      if let some ref := ref then
        throwErrorAt ref "tactic '{ref}' failed, but got different error message:\n\n{err}"
      else
        throwError "tactic failed, but got different error message:\n\n{err}"
  else
    if let some ref := ref then
      throwErrorAt ref "tactic '{ref}' succeeded, but was expected to fail"
    else
      throwError "tactic succeeded, but was expected to fail"
elab_rules : tactic
| `(tactic| success_if_fail_with_msg $msg:term $tacs:tacticSeq) =>
  Term.withoutErrToSorry <| withoutRecover do
    let msg ← unsafe Term.evalTerm String (.const ``String []) msg
    successIfFailWithMessage msg (evalTacticSeq tacs) tacs
end Mathlib.Tactic