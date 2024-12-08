import Mathlib.Init
import Lean.Elab.SyntheticMVars
open Lean Meta Elab
namespace Lean.Expr
def cleanConsts : List Name :=
  [``id]
def clean (e : Expr) : Expr :=
  e.replace fun
    | .app (.app (.const n _) _) e' => if n ∈ cleanConsts then some e' else none
    | .app (.lam _ _ (.bvar 0) _) e' => some e'
    | e =>
      match e.letFun? with
      | some (_n, _t, v, .bvar 0) => some v
      | _ => none
end Lean.Expr
namespace Mathlib.Tactic
syntax (name := cleanStx) "clean% " term : term
@[term_elab cleanStx, inherit_doc cleanStx]
def elabClean : Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(clean% $t) => do
    let e ← Term.withSynthesize <| Term.elabTerm t expectedType?
    return (← instantiateMVars e).clean
  | _ => throwUnsupportedSyntax
macro "clean " t:term : tactic => `(tactic| exact clean% $t)
end Mathlib.Tactic