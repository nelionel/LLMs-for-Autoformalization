import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Util.AddRelatedDecl
open Lean Meta Elab Tactic
open Mathlib.Tactic
namespace CategoryTheory
def catAppSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [
    ``Cat.whiskerLeft_app, ``Cat.whiskerRight_app, ``Cat.id_app, ``Cat.comp_app,
    ``Cat.eqToHom_app] e
    (config := { decide := false })
def toCatExpr (e : Expr) : MetaM Expr := do
  let (args, binderInfos, conclusion) ← forallMetaTelescope (← inferType e)
  let B ←
    match conclusion.getAppFnArgs with
    | (`Eq, #[_, η, _]) =>
      match (← inferType η).getAppFnArgs with
      | (`Quiver.Hom, #[_, _, f, _]) =>
        match (← inferType f).getAppFnArgs with
        | (`Quiver.Hom, #[_, _, a, _]) => inferType a
        | _ => throwError "The conclusion {conclusion} is not an equality of 2-morphisms!"
      | _ => throwError "The conclusion {conclusion} is not an equality of 2-morphisms!"
    | _ => throwError "The conclusion {conclusion} is not an equality!"
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let _ ← isDefEq B (.const ``Cat [v, u])
  let some inst ← args.findM? fun x => do
      return (← inferType x).getAppFnArgs == (`CategoryTheory.Bicategory, #[B])
    | throwError "Can not find the argument for the bicategory instance of the bicategory in which \
      the equality is taking place."
  let _ ← isDefEq inst (.const ``CategoryTheory.Cat.bicategory [v, u])
  let value := mkAppN e args
  let rec
    apprec (i : Nat) (e : Expr) : MetaM Expr := do
      if i < args.size then
        let arg := args[i]!
        let bi := binderInfos[i]!
        let e' ← apprec (i + 1) e
        unless arg != B && arg != inst do return e'
        mkLambdaFVars #[arg] e' (binderInfoForMVars := bi)
      else
        return e
  let value ← apprec 0 value
  return value
def toAppExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType catAppSimp (← mkAppM ``NatTrans.congr_app #[e])) e
syntax (name := to_app) "to_app" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr
initialize registerBuiltinAttribute {
  name := `to_app
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_app $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`to_app` can only be used as a global attribute"
    addRelatedDecl src "_app" ref stx? fun type value levels => do
      let levelMVars ← levels.mapM fun _ => mkFreshLevelMVar
      let value ← mkExpectedTypeHint value type
      let value := value.instantiateLevelParams levels levelMVars
      let newValue ← toAppExpr (← toCatExpr value)
      let r := (← getMCtx).levelMVarToParam (fun _ => false) (fun _ => false) newValue
      let output := (r.expr, r.newParamNames.toList)
      pure output
  | _ => throwUnsupportedSyntax }
open Term in
elab "to_app_of% " t:term : term => do
  toAppExpr (← elabTerm t none)
end CategoryTheory