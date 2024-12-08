import Mathlib.Tactic.Core
import Mathlib.Tactic.FunProp
import Aesop
declare_aesop_rule_sets [CStarAlgebra]
syntax (name := cfcTac) "cfc_tac" : tactic
macro_rules
  | `(tactic| cfc_tac) => `(tactic|
         try (first |
              assumption |
              infer_instance |
              aesop (rule_sets := [$(Lean.mkIdent `CStarAlgebra):ident])))
syntax (name := cfcContTac) "cfc_cont_tac" : tactic
macro_rules
  | `(tactic| cfc_cont_tac) =>
    `(tactic| try (first
      | fun_prop (disch := aesop (config := {warnOnNonterminal := false})
          (rule_sets := [$(Lean.mkIdent `CStarAlgebra):ident]))
      | assumption))
syntax (name := cfcZeroTac) "cfc_zero_tac" : tactic
macro_rules
  | `(tactic| cfc_zero_tac) =>
      `(tactic| try
          (first | aesop (rule_sets := [$(Lean.mkIdent `CStarAlgebra):ident]) | assumption))