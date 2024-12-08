import Batteries.Tactic.Lint
import Mathlib.Tactic.DeclarationNames
namespace Batteries.Tactic.Lint
open Lean Meta
@[env_linter] def structureInType : Linter where
  noErrorsFound := "no structures that should be in Prop found."
  errorsFound := "FOUND STRUCTURES THAT SHOULD BE IN PROP."
  test declName := do
    unless isStructure (← getEnv) declName do return none
    let isProp ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun _ ty ↦ return ty == .sort .zero
    if isProp then return none
    let projs := (getStructureInfo? (← getEnv) declName).get!.fieldNames
    if projs.isEmpty then return none 
    let allProofs ← projs.allM (do isProof <| ← mkConstWithLevelParams <| declName ++ ·)
    unless allProofs do return none
    return m!"all fields are propositional but the structure isn't."
@[env_linter] def deprecatedNoSince : Linter where
  noErrorsFound := "no `deprecated` tags without `since` dates."
  errorsFound := "FOUND `deprecated` tags without `since` dates."
  test declName := do
    let some info := Lean.Linter.deprecatedAttr.getParam? (← getEnv) declName | return none
    match info.since? with
    | some _ => return none 
    | none => return m!"`deprecated` attribute without `since` date"
end Batteries.Tactic.Lint
namespace Mathlib.Linter
register_option linter.dupNamespace : Bool := {
  defValue := true
  descr := "enable the duplicated namespace linter"
}
namespace DupNamespaceLinter
open Lean Parser Elab Command Meta
@[inherit_doc linter.dupNamespace]
def dupNamespace : Linter where run := withSetOptionIn fun stx ↦ do
  if Linter.getLinterValue linter.dupNamespace (← getOptions) then
    let mut aliases := #[]
    if let some exp := stx.find? (·.isOfKind `Lean.Parser.Command.export) then
      aliases ← getAliasSyntax exp
    for id in (← getNamesFrom (stx.getPos?.getD default)) ++ aliases do
      let declName := id.getId
      if declName.hasMacroScopes then continue
      let nm := declName.components
      let some (dup, _) := nm.zip (nm.tailD []) |>.find? fun (x, y) ↦ x == y
        | continue
      Linter.logLint linter.dupNamespace id
        m!"The namespace '{dup}' is duplicated in the declaration '{declName}'"
initialize addLinter dupNamespace
end Mathlib.Linter.DupNamespaceLinter