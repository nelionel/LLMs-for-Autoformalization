import Mathlib.Tactic.TermCongr
namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta
initialize registerTraceClass `Tactic.congrm
  sorry
  sorry
  sorry
example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm fun x => ∀ w, ?_ + a = w
  exact h
```
The `congrm` command is a convenient frontend to `congr(...)` congruence quotations.
If the goal is an equality, `congrm e` is equivalent to `refine congr(e')` where `e'` is
built from `e` by replacing each placeholder `?m` by `$(?m)`.
The pattern `e` is allowed to contain `$(...)` expressions to immediately substitute
equality proofs into the congruence, just like for congruence quotations.
-/
syntax (name := congrM) "congrm " term : tactic
elab_rules : tactic
  | `(tactic| congrm $expr:term) => do
    let pattern ← expr.raw.replaceM fun stx =>
      if stx.isOfKind ``Parser.Term.syntheticHole then
        pure <| stx.mkAntiquotNode `term
      else if stx.isAntiquots then
        pure stx
      else
        pure none
    trace[Tactic.congrm] "pattern: {pattern}"
    liftMetaTactic fun g => do
      return [← (← g.iffOfEq).liftReflToEq]
    withMainContext do
      let gStx ← Term.exprToSyntax (← getMainTarget)
      evalTactic <| ← `(tactic| refine (congr($(⟨pattern⟩)) : $gStx))
end Mathlib.Tactic