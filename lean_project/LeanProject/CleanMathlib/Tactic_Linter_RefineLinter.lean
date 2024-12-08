import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header
open Lean Elab
namespace Mathlib.Linter
register_option linter.refine : Bool := {
  defValue := false
  descr := "enable the refine linter"
}
partial
def getRefine' : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let rargs := (args.map getRefine').flatten
    if kind == ``Lean.Parser.Tactic.refine' then rargs.push stx else rargs
  | _ => default
@[inherit_doc linter.refine]
def refineLinter : Linter where run := withSetOptionIn fun _stx => do
  unless Linter.getLinterValue linter.refine (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stx in (getRefine' _stx) do
    Linter.logLint linter.refine stx
      "The `refine'` tactic is discouraged: \
      please strongly consider using `refine` or `apply` instead."
initialize addLinter refineLinter
end Mathlib.Linter