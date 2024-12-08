import Mathlib.Init
import Lean.Widget.InteractiveGoal
import Lean.Elab.Deriving.Basic
open Lean Meta Server
class SelectInsertParamsClass (α : Type) where
  pos : α → Lsp.Position
  goals : α → Array Widget.InteractiveGoal
  selectedLocations : α → Array SubExpr.GoalsLocation
  replaceRange : α → Lsp.Range
namespace Lean.Elab
open Command Meta Parser Term
private def mkSelectInsertParamsInstance (declName : Name) : TermElabM Syntax.Command :=
  `(command|instance : SelectInsertParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.pos, fun prop => prop.goals,
     fun prop => prop.selectedLocations, fun prop => prop.replaceRange⟩)
def mkSelectInsertParamsInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkSelectInsertParamsInstance declName)
    return true
  else
    return false
initialize registerDerivingHandler ``SelectInsertParamsClass mkSelectInsertParamsInstanceHandler
end Lean.Elab