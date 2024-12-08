import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header
open Lean Elab
namespace Mathlib.Linter
register_option linter.docPrime : Bool := {
  defValue := false
  descr := "enable the docPrime linter"
}
namespace DocPrime
@[inherit_doc Mathlib.Linter.linter.docPrime]
def docPrimeLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.docPrime (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind do return
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.private)).isSome then return
  let docstring := stx[0][0]
  let declId :=
    if stx[1].isOfKind ``Lean.Parser.Command.instance then
      stx[1][3][0]
    else
      stx[1][1]
  let declName : Name :=
    if let `_root_ :: rest := declId[0].getId.components then
      rest.foldl (· ++ ·) default
    else (← getCurrNamespace) ++ declId[0].getId
  let msg := m!"`{declName}` is missing a doc-string, please add one.\n\
      Declarations whose name ends with a `'` are expected to contain an explanation for the \
      presence of a `'` in their doc-string. This may consist of discussion of the difference \
      relative to the unprimed version, or an explanation as to why no better naming scheme \
      is possible."
  if docstring[0][1].getAtomVal.isEmpty && declName.toString.back == '\'' then
    if ← System.FilePath.pathExists "scripts/nolints_prime_decls.txt" then
      if (← IO.FS.lines "scripts/nolints_prime_decls.txt").contains declName.toString then
        return
      else
        Linter.logLint linter.docPrime declId msg
    else
      Linter.logLint linter.docPrime declId msg
initialize addLinter docPrimeLinter
end DocPrime
end Mathlib.Linter