import Mathlib.Tactic.Positivity.Core
open Aesop.BuiltinRules in
attribute [aesop (rule_sets := [finiteness]) safe -50] assumption intros
set_option linter.unusedTactic false in
add_aesop_rules safe tactic (rule_sets := [finiteness]) (by positivity)
macro (name := finiteness) "finiteness" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { introsTransparency? := some .reducible, terminal := true, enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `finiteness):ident, -default, -builtin]))
macro (name := finiteness?) "finiteness?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { introsTransparency? := some .reducible, terminal := true, enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `finiteness):ident, -default, -builtin]))
macro (name := finiteness_nonterminal) "finiteness_nonterminal" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { introsTransparency? := some .reducible, terminal := false, enableSimp := false,
                 warnOnNonterminal := false  })
    (rule_sets := [$(Lean.mkIdent `finiteness):ident, -default, -builtin]))