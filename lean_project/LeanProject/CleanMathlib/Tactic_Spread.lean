import Mathlib.Init
import Lean.Elab.Binders
open Lean Parser.Term Macro
syntax (name := letImplDetailStx) "let_impl_detail " ident " := " term "; " term : term
open Lean Elab Term Meta
@[term_elab letImplDetailStx, inherit_doc letImplDetailStx]
def elabLetImplDetail : TermElab := fun stx expectedType? =>
  match stx with
  | `(let_impl_detail $id := $valStx; $body) => do
    let val ← elabTerm valStx none
    let type ← inferType val
    trace[Elab.let.decl] "{id.getId} : {type} := {val}"
    let result ←
      withLetDecl id.getId (kind := .default) type val fun x => do
        addLocalVarInfo id x
        let lctx ← getLCtx
        let lctx := lctx.modifyLocalDecl x.fvarId! fun decl => decl.setKind .implDetail
        withLCtx lctx (← getLocalInstances) do
          let body ← elabTermEnsuringType body expectedType?
          let body ← instantiateMVars body
          mkLetFVars #[x] body (usedLetOnly := false)
    pure result
  | _ => throwUnsupportedSyntax
macro_rules
| `({ $[$srcs,* with]? $[$fields],* $[: $ty?]? }) => show MacroM Term from do
    let mut spreads := #[]
    let mut newFields := #[]
    for field in fields do
      match field.1 with
        | `(structInstField| $name:ident := $arg) =>
          if name.getId.eraseMacroScopes == `__ then do
            spreads := spreads.push arg
          else
            newFields := newFields.push field
        | _ =>
          throwUnsupported
    if spreads.isEmpty then throwUnsupported
    let spreadData ← withFreshMacroScope <| spreads.mapIdxM fun i spread => do
      let n := Name.num `__spread i
      return (mkIdent <| ← Macro.addMacroScope n, spread)
    let srcs := (srcs.map (·.getElems)).getD {} ++ spreadData.map Prod.fst
    let body ← `({ $srcs,* with $[$newFields],* $[: $ty?]? })
    spreadData.foldrM (init := body) fun (id, val) body => `(let_impl_detail $id := $val; $body)