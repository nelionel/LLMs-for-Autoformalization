import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header
open Lean Elab
namespace Mathlib.Linter.Style
def is_obtain_without_proof : Syntax → Bool
  | `(tactic|obtain : $_type) | `(tactic|obtain $_pat : $_type) => true
  | _ => false
register_option linter.oldObtain : Bool := {
  defValue := false
  descr := "enable the `oldObtain` linter"
}
def oldObtainLinter : Linter where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.oldObtain (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some head := stx.find? is_obtain_without_proof then
      Linter.logLint linter.oldObtain head m!"Please remove stream-of-conciousness `obtain` syntax"
initialize addLinter oldObtainLinter
end Mathlib.Linter.Style