import Mathlib.Init
import Lean.Elab.DeclarationRange
import Lean.Elab.Term
open Lean Meta Elab
namespace Mathlib.Tactic
def addRelatedDecl (src : Name) (suffix : String) (ref : Syntax)
    (attrs? : Option (Syntax.TSepArray `Lean.Parser.Term.attrInstance ","))
    (construct : Expr → Expr → List Name → MetaM (Expr × List Name)) :
    MetaM Unit := do
  let tgt := match src with
    | Name.str n s => Name.mkStr n <| s ++ suffix
    | x => x
  addDeclarationRangesFromSyntax tgt (← getRef) ref
  let info ← getConstInfo src
  let (newValue, newLevels) ← construct info.type info.value! info.levelParams
  let newValue ← instantiateMVars newValue
  let newType ← instantiateMVars (← inferType newValue)
  match info with
  | ConstantInfo.thmInfo info =>
    addAndCompile <| .thmDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
  | ConstantInfo.defnInfo info =>
    addAndCompile <| if ← isProp newType then .thmDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
      else .defnDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
  | _ => throwError "Constant {src} is not a theorem or definition."
  if isProtected (← getEnv) src then
    setEnv <| addProtected (← getEnv) tgt
  let attrs := match attrs? with | some attrs => attrs | none => #[]
  _ ← Term.TermElabM.run' <| do
    let attrs ← elabAttrs attrs
    Term.applyAttributes src attrs
    Term.applyAttributes tgt attrs
end Mathlib.Tactic