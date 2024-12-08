import Mathlib.Init
import Lean.Elab.Command
import Mathlib.Util.AssertExistsExt
section
open Lean Elab Meta Command
namespace Mathlib.AssertNotExist
elab "#check_assertions" tk:("!")?: command => do
  let env ← getEnv
  let entries := env.getSortedAssertExists
  if entries.isEmpty && tk.isNone then logInfo "No assertions made." else
  let allMods := env.allImportedModuleNames
  let mut msgs := #[m!""]
  let mut outcome := m!""
  let mut allExist? := true
  for d in entries do
    let type := if d.isDecl then "declaration" else "module"
    let cond := if d.isDecl then env.contains d.givenName else allMods.contains d.givenName
    outcome := if cond then m!"{checkEmoji}" else m!"{crossEmoji}"
    allExist? := allExist? && cond
    if tk.isNone || !cond then
      msgs := msgs.push m!"{outcome} '{d.givenName}' ({type}) asserted in '{d.modName}'."
  msgs := msgs.push m!"
    |>.push m!"{checkEmoji} means the declaration or import exists."
    |>.push m!"{crossEmoji} means the declaration or import does not exist."
  let msg := MessageData.joinSep msgs.toList "\n"
  if allExist? && tk.isNone then
    logInfo msg
  if !allExist? then
    logWarning msg
end Mathlib.AssertNotExist
elab "assert_exists " n:ident : command => do
  let _ ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
elab "assert_not_exists " n:ident : command => do
  let decl ←
    try liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    catch _ =>
      Mathlib.AssertNotExist.addDeclEntry true n.getId (← getMainModule)
      return
  let env ← getEnv
  let c ← mkConstWithLevelParams decl
  let msg ← (do
    let mut some idx := env.getModuleIdxFor? decl
      | pure m!"Declaration {c} is defined in this file."
    let mut msg := m!"Declaration {c} is not allowed to be imported by this file.\n\
      It is defined in {env.header.moduleNames[idx.toNat]!},"
    for i in [idx.toNat+1:env.header.moduleData.size] do
      if env.header.moduleData[i]!.imports.any (·.module == env.header.moduleNames[idx.toNat]!) then
        idx := i
        msg := msg ++ m!"\n  which is imported by {env.header.moduleNames[i]!},"
    pure <| msg ++ m!"\n  which is imported by this file.")
  throw <| .error n m!"{msg}\n\n\
    These invariants are maintained by `assert_not_exists` statements, \
    and exist in order to ensure that \"complicated\" parts of the library \
    are not accidentally introduced as dependencies of \"simple\" parts of the library."
elab "assert_not_imported " ids:ident+ : command => do
  let mods := (← getEnv).allImportedModuleNames
  for id in ids do
    if mods.contains id.getId then
      logWarningAt id m!"the module '{id}' is (transitively) imported"
    else
      Mathlib.AssertNotExist.addDeclEntry false id.getId (← getMainModule)
end