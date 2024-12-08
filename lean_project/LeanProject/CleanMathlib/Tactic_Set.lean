import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
namespace Mathlib.Tactic
open Lean Elab Elab.Tactic Meta
syntax setArgsRest := ppSpace ident (" : " term)? " := " term (" with " "← "? ident)?
syntax (name := setTactic) "set" "!"? setArgsRest : tactic
macro "set!" rest:setArgsRest : tactic => `(tactic| set ! $rest:setArgsRest)
```
-/
elab_rules : tactic
| `(tactic| set%$tk $[!%$rw]? $a:ident $[: $ty:term]? := $val:term $[with $[←%$rev]? $h:ident]?) =>
  withMainContext do
    let (ty, vale) ← match ty with
    | some ty =>
      let ty ← Term.elabType ty
      pure (ty, ← elabTermEnsuringType val ty)
    | none =>
      let val ← elabTerm val none
      pure (← inferType val, val)
    let fvar ← liftMetaTacticAux fun goal ↦ do
      let (fvar, goal) ← (← goal.define a.getId ty vale).intro1P
      pure (fvar, [goal])
    withMainContext <|
      Term.addTermInfo' (isBinder := true) a (mkFVar fvar)
    if rw.isNone then
      evalTactic (← `(tactic| try rewrite [show $(← Term.exprToSyntax vale) = $a from rfl] at *))
    match h, rev with
    | some h, some none =>
      evalTactic (← `(tactic| have%$tk
        $h : $a = ($(← Term.exprToSyntax vale) : $(← Term.exprToSyntax ty)) := rfl))
    | some h, some (some _) =>
      evalTactic (← `(tactic| have%$tk
        $h : ($(← Term.exprToSyntax vale) : $(← Term.exprToSyntax ty)) = $a := rfl))
    | _, _ => pure ()
end Mathlib.Tactic