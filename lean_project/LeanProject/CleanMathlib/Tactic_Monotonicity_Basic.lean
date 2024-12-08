import Lean.Elab.Tactic.SolveByElim
import Mathlib.Tactic.Monotonicity.Attr
open Lean Elab Tactic Parser Tactic
open Tactic SolveByElim
namespace Mathlib.Tactic.Monotonicity
syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic
elab_rules : tactic
| `(tactic| mono $[*]? $[$h:mono.side]? $[ with%$w $a:term,*]? $[ using%$u $s,*]? ) => do
  let msg (s : String) := s ++ " syntax is not yet supported in 'mono'"
  if let some h := h then throwErrorAt h (msg "'left'/'right'/'both'")
  if let some w := w then throwErrorAt w (msg "'with'")
  if let some u := u then throwErrorAt u (msg "'using'")
  let cfg := { { : Meta.SolveByElim.ApplyRulesConfig } with
    backtracking := false
    transparency := .reducible
    exfalso := false }
  liftMetaTactic fun g => do processSyntax cfg false false [] [] #[mkIdent `mono] [g]
end Monotonicity
end Mathlib.Tactic