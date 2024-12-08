import Mathlib.Tactic.Measurability.Init
import Mathlib.Algebra.Group.Defs
open Lean.Parser.Tactic (optConfig)
attribute [aesop (rule_sets := [Measurable]) unfold norm] Function.comp
attribute [aesop (rule_sets := [Measurable]) norm] npowRec
macro "measurability" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Measurable):ident]))
macro "measurability" : tactic =>
  `(tactic| aesop (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Measurable):ident]))
macro "measurability?" : tactic =>
  `(tactic| aesop? (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Measurable):ident]))
syntax (name := measurability!) "measurability!" : tactic
syntax (name := measurability!?) "measurability!?" : tactic