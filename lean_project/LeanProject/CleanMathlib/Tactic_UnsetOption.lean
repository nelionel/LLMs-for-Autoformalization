import Mathlib.Init
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Elab.Command
namespace Lean.Elab
variable {m : Type → Type} [Monad m] [MonadOptions m] [MonadRef m] [MonadInfoTree m]
def elabUnsetOption (id : Syntax) : m Options := do
  addCompletionInfo <| CompletionInfo.option (← getRef)
  unsetOption id.getId.eraseMacroScopes
where
  unsetOption (optionName : Name) : m Options := return (← getOptions).erase optionName
namespace Command
elab (name := unsetOption) "unset_option " opt:ident : command => do
  let options ← Elab.elabUnsetOption opt
  modify fun s ↦ { s with maxRecDepth := maxRecDepth.get options }
  modifyScope fun scope ↦ { scope with opts := options }
end Command
end Lean.Elab