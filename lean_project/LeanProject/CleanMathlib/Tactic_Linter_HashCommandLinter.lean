import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header
namespace Mathlib.Linter
register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "enable the `#`-command linter"
}
namespace HashCommandLinter
open Lean Elab
open Command in
private partial def withSetOptionIn' (cmd : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in then
    if stx[0].getKind == ``Lean.Parser.Command.set_option then
      let opts ← Elab.elabSetOption stx[0][1] stx[0][3]
      withScope (fun scope => { scope with opts }) do
        withSetOptionIn' cmd stx[2]
    else
      withSetOptionIn' cmd stx[2]
  else
    cmd stx
private abbrev allowed_commands : Std.HashSet String := { "#adaptation_note" }
def hashCommandLinter : Linter where run := withSetOptionIn' fun stx => do
  let mod := (← getMainModule).components
  if Linter.getLinterValue linter.hashCommand (← getOptions) &&
    ((← get).messages.toList.isEmpty || warningAsError.get (← getOptions)) &&
    (mod.getD 0 default != `test || (mod == [`test, `HashCommandLinter]))
    then
    if let some sa := stx.getHead? then
      let a := sa.getAtomVal
      if (a.get ⟨0⟩ == '#' && ! allowed_commands.contains a) then
        let msg := m!"`#`-commands, such as '{a}', are not allowed in 'Mathlib'"
        if warningAsError.get (← getOptions) then
          logInfoAt sa (msg ++ " [linter.hashCommand]")
        else Linter.logLint linter.hashCommand sa msg
initialize addLinter hashCommandLinter
end HashCommandLinter