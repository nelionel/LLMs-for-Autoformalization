import Mathlib.Init
import Lean.Elab.Tactic.Basic
open Lean Meta Elab Tactic
elab (name := guardGoalNums) "guard_goal_nums " n:num : tactic => do
  let numGoals := (← getGoals).length
  guard (numGoals = n.getNat) <|>
    throwError "expected {n.getNat} goals but found {numGoals}"