import Mathlib.Init
import Lean.Elab.Term
namespace Mathlib.Util.TermBeta
open Lean Elab Term
syntax (name := betaStx) "beta% " term : term
@[term_elab betaStx, inherit_doc betaStx]
def elabBeta : TermElab := fun stx expectedType? =>
  match stx with
  | `(beta% $t) => do
    let e ← elabTerm t expectedType?
    return (← instantiateMVars e).headBeta
  | _ => throwUnsupportedSyntax
end Mathlib.Util.TermBeta