import Mathlib.Init
namespace Mathlib.PPWithUniv
open Lean Parser PrettyPrinter Delaborator SubExpr Elab Command
def delabWithUniv : Delab :=
  whenPPOption (·.get pp.universes.name true) <|
  let enablePPUnivOnHead subExpr :=
    let expr := subExpr.expr
    let expr := mkAppN (expr.getAppFn.setOption pp.universes.name true) expr.getAppArgs
    { subExpr with expr }
  withTheReader SubExpr enablePPUnivOnHead delabApp
syntax (name := ppWithUnivAttr) "pp_with_univ" : attr
initialize registerBuiltinAttribute {
  name := `ppWithUnivAttr
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| pp_with_univ) => do
    liftCommandElabM <| withRef ref do
      let attr ← Elab.elabAttr <| ← `(Term.attrInstance| delab $(mkIdent <| `app ++ src))
      liftTermElabM <| Term.applyAttributes ``delabWithUniv #[{attr with kind}]
  | _ => throwUnsupportedSyntax }
end PPWithUniv
end Mathlib