import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.Cleanup
import Lean.PrettyPrinter
import Batteries.Lean.Meta.Inaccessible
```
* TODO: Add tactic code actions?
* Output may produce lines with more than 100 characters
### Caveat
Tl;dr: sometimes, using `set_option [your pp option] in extract_goal` may work where `extract_goal`
does not.
The extracted goal may depend on imports and `pp` options, since it relies on delaboration.
For this reason, the extracted goal may not be equivalent to the given goal.
However, the tactic responds to pretty printing options.
For example, calling `set_option pp.all true in extract_goal` in the examples below actually works.
```lean
theorem int_eq_nat {z : Int} : ∃ n, Int.ofNat n = z := sorry
example {z : Int} : ∃ n : Nat, ↑n = z := by
  extract_goal  
  apply int_eq_nat  
```
However, importing `Batteries.Classes.Cast`, makes `extract_goal` produce a different theorem
```lean
import Batteries.Classes.Cast
theorem extracted_1 {z : Int} : ∃ n, ↑n = z := ⟨_, rfl⟩
example {z : Int} : ∃ n : Nat, ↑n = z := by
  extract_goal
  apply extracted_1
```
Similarly, the extracted goal may fail to type-check:
```lean
example (a : α) : ∃ f : α → α, f a = a := by
  extract_goal
  exact ⟨id, rfl⟩
theorem extracted_1.{u_1} {α : Sort u_1} (a : α) : ∃ f, f a = a := sorry
```
and also
```lean
import Mathlib.Algebra.Polynomial.Basic
theorem extracted_1 : X = X := sorry
example : (X : Nat[X]) = X := by
  extract_goal
```
-/
namespace Mathlib.Tactic.ExtractGoal
open Lean Elab Tactic Meta
syntax star := "*"
syntax config := star <|> (colGt ppSpace ident)*
syntax (name := extractGoal) "extract_goal" config (" using " ident)? : tactic
elab_rules : tactic
  | `(tactic| extract_goal $cfg:config $[using $name?]?) => do
    let name ← if let some name := name?
                then pure name.getId
                else mkAuxName ((← getCurrNamespace) ++ `extracted) 1
    let msg ← withoutModifyingEnv <| withoutModifyingState do
      let g ← getMainGoal
      let g ← do match cfg with
        | `(config| *) => pure g
        | `(config| ) =>
          if (← g.getType >>= instantiateMVars).consumeMData.isConstOf ``False then
            pure g
          else
            g.cleanup
        | `(config| $fvars:ident*) =>
          g.cleanup (toPreserve := (← getFVarIds fvars)) (indirectProps := false)
        | _ => throwUnsupportedSyntax
      let (g, _) ← g.renameInaccessibleFVars
      let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
      let ty ← instantiateMVars (← g.getType)
      if ty.hasExprMVar then
        throwError "Extracted goal has metavariables: {ty}"
      let ty ← Term.levelMVarToParam ty
      let seenLevels := collectLevelParams {} ty
      let levels := (← Term.getLevelNames).filter
                      fun u => seenLevels.visitedLevel.contains (.param u)
      addAndCompile <| Declaration.axiomDecl
        { name := name
          levelParams := levels
          isUnsafe := false
          type := ty }
      let sig ← addMessageContext <| MessageData.signature name
      let cmd := if ← Meta.isProp ty then "theorem" else "def"
      pure m!"{cmd} {sig} := sorry"
    logInfo msg
end Mathlib.Tactic.ExtractGoal