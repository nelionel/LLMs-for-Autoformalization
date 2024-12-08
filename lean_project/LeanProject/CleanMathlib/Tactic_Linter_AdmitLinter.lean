import Lean.Elab.Command
import Mathlib.Init
namespace Mathlib.Linter
register_option linter.admit : Bool := {
  defValue := false
  descr := "enable the admit linter"
}
namespace AdmitLinter
open Lean Elab
partial
def getAdmit (stx : Syntax) : Array Syntax :=
  if let `(tactic| admit) := stx then
    #[stx]
  else
    stx.foldArgs (fun arg r => r ++ getAdmit arg) #[]
def admitLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.admit (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stxAdmit in (getAdmit stx) do
    Linter.logLint linter.admit stxAdmit
      "The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead."
initialize addLinter admitLinter
end AdmitLinter
end Mathlib.Linter