import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Eval
open Lean Meta Elab Tactic
elab (name := Lean.Parser.Tactic.trace) tk:"trace " val:term : tactic => do
  let e ← elabTerm (← `(toString $val)) (some (mkConst `String))
  logInfoAt tk <|← unsafe evalExpr String (mkConst `String) e