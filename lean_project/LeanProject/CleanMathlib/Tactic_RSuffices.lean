import Mathlib.Tactic.Basic
namespace Mathlib.Tactic
syntax (name := rsuffices) "rsuffices"
  (ppSpace Lean.Parser.Tactic.rcasesPatMed)? (" : " term)? (" := " term,+)? : tactic
macro_rules
| `(tactic| rsuffices $[$pred]? $[: $foo]? $[:= $bar]?) =>
`(tactic | (obtain $[$pred]? $[: $foo]? $[:= $bar]?; rotate_left))
end Mathlib.Tactic