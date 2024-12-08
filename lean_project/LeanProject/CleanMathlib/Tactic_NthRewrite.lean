import Mathlib.Init
import Lean.Elab.Tactic.Rewrite
namespace Mathlib.Tactic
open Lean Elab Tactic Meta Parser.Tactic
```
Notice that the second occurrence of `a` from the left has been rewritten by `nth_rewrite`.
To understand the importance of order of precedence, consider the example below
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] 
```
Here, although the occurrence parameter is `2`, `(a + b)` is rewritten to `(b + a)`. This happens
because in order of precedence, the first occurrence of `_ + _` is the one that adds `a + b` to `c`.
The occurrence in `a + b` counts as the second occurrence.
If a term `t` is introduced by rewriting with `eqᵢ`, then this instance of `t` will be counted as an
_occurrence_ of `t` for all subsequent rewrites of `t` with `eqⱼ` for `j > i`. This behaviour is
illustrated by the example below
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rewrite 3 [h, h]
```
Here, the first `nth_rewrite` with `h` introduces an additional occurrence of `a` in the goal.
That is, the goal state after the first rewrite looks like below
```lean
```
This new instance of `a` also turns out to be the third _occurrence_ of `a`.  Therefore,
the next `nth_rewrite` with `h` rewrites this `a`.
-/
syntax (name := nthRewriteSeq) "nth_rewrite" optConfig ppSpace num+ rwRuleSeq (location)? : tactic
@[inherit_doc nthRewriteSeq, tactic nthRewriteSeq] def evalNthRewriteSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| nth_rewrite $cfg:optConfig $[$n]* $_rules:rwRuleSeq $[$loc]?) =>
    let cfg ← elabRewriteConfig cfg
    let loc := expandOptLocation (mkOptionalNode loc)
    let occ := Occurrences.pos (n.map TSyntax.getNat).toList
    let cfg := { cfg with occs := occ }
    withRWRulesSeq stx[0] stx[3] fun symm term => do
      withLocation loc
        (rewriteLocalDecl term symm · cfg)
        (rewriteTarget term symm cfg)
        (throwTacticEx `nth_rewrite · "did not find instance of the pattern in the current goal")
  | _ => throwUnsupportedSyntax
```
Notice that the second occurrence of `a` from the left has been rewritten by `nth_rewrite`.
To understand the importance of order of precedence, consider the example below
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] 
```
Here, although the occurrence parameter is `2`, `(a + b)` is rewritten to `(b + a)`. This happens
because in order of precedence, the first occurrence of `_ + _` is the one that adds `a + b` to `c`.
The occurrence in `a + b` counts as the second occurrence.
If a term `t` is introduced by rewriting with `eqᵢ`, then this instance of `t` will be counted as an
_occurrence_ of `t` for all subsequent rewrites of `t` with `eqⱼ` for `j > i`. This behaviour is
illustrated by the example below
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rw 3 [h, h]
```
Here, the first `nth_rw` with `h` introduces an additional occurrence of `a` in the goal. That is,
the goal state after the first rewrite looks like below
```lean
```
This new instance of `a` also turns out to be the third _occurrence_ of `a`.  Therefore,
the next `nth_rw` with `h` rewrites this `a`.
Further, `nth_rw` will close the remaining goal with `rfl` if possible.
-/
macro (name := nthRwSeq) "nth_rw" c:optConfig ppSpace n:num+ s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    `(tactic| (nth_rewrite $c:optConfig $[$n]* [$rs,*] $(l)?; with_annotate_state $rbrak
      (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported
end Mathlib.Tactic