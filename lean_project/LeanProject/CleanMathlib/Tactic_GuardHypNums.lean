import Mathlib.Init
import Lean.Elab.Tactic.Basic
open Lean Meta Elab Tactic
elab (name := guardHypNums) "guard_hyp_nums " n:num : tactic => do
  let numHyps := (← getLCtx).size
  guard (numHyps = n.getNat) <|>
    throwError "expected {n.getNat} hypotheses but found {numHyps}"