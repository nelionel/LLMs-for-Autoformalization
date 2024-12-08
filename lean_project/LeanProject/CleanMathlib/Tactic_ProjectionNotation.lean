import Lean.Elab.AuxDef
import Mathlib.Init
namespace Mathlib.ProjectionNotation
open Lean Parser Elab Term
open PrettyPrinter.Delaborator SubExpr
open Lean.Elab.Command
def mkExtendedFieldNotationUnexpander (f : Name) : CommandElabM Unit := do
  let .str A projName := f | throwError "Projection name must end in a string component."
  if let some _ := getStructureInfo? (← getEnv) A then
    let .str _ A' := A | throwError "{A} must end in a string component"
    let toA : Name := .str .anonymous ("to" ++ A')
    elabCommand <| ← `(command|
      @[app_unexpander $(mkIdent f)]
      aux_def $(mkIdent <| Name.str f "unexpander") : Lean.PrettyPrinter.Unexpander := fun
        | `($$_ $$(x).$(mkIdent toA))
        | `($$_ $$x) => set_option hygiene false in `($$(x).$(mkIdent (.mkSimple projName)))
        | _ => throw ())
  else
    elabCommand <| ← `(command|
      @[app_unexpander $(mkIdent f)]
      aux_def $(mkIdent <| Name.str f "unexpander") : Lean.PrettyPrinter.Unexpander := fun
        | `($$_ $$x) => set_option hygiene false in `($$(x).$(mkIdent (.mkSimple projName)))
        | _ => throw ())
syntax (name := ppDotAttr) "pp_dot" : attr
initialize registerBuiltinAttribute {
  name := `ppDotAttr
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| pp_dot) => do
    logWarning "\
      The @[pp_dot] attribute is deprecated now that dot notation is the default \
      with the introduction of `pp.fieldNotation.generalized` in Lean v4.8.0."
    if (kind != AttributeKind.global) then
      throwError "`pp_dot` can only be used as a global attribute"
    liftCommandElabM <| withRef ref <| mkExtendedFieldNotationUnexpander src
  | _ => throwUnsupportedSyntax }
end Mathlib.ProjectionNotation