import Batteries.Tactic.Init
import Mathlib.Tactic.PushNeg
open Lean Lean.Parser Parser.Tactic Elab Command Elab.Tactic Meta
syntax (name := byContra!) "by_contra!" (ppSpace colGt binderIdent)? Term.optType : tactic
macro_rules
  | `(tactic| by_contra!%$tk $[_%$under]? $[: $ty]?) =>
    `(tactic| by_contra! $(mkIdentFrom (under.getD tk) `this (canonical := true)):ident $[: $ty]?)
  | `(tactic| by_contra! $e:ident) => `(tactic| (by_contra $e:ident; try push_neg at $e:ident))
  | `(tactic| by_contra! $e:ident : $y) => `(tactic|
       (by_contra! h
        have $e:ident : $y := by { (try push_neg); exact h }
        clear h))