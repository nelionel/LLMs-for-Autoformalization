import Mathlib.Tactic.Have
namespace Mathlib.Tactic
open Lean Elab.Tactic
syntax (name := replace') "replace" haveIdLhs' : tactic
elab_rules : tactic
| `(tactic| replace $n:optBinderIdent $bs* $[: $t:term]?) => withMainContext do
    let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false
    let name := optBinderIdent.name n
    let hId? := (← getLCtx).findFromUserName? name |>.map fun d ↦ d.fvarId
    match hId? with
    | some hId => replaceMainGoal [goal1, (← observing? <| goal2.clear hId).getD goal2]
    | none     => replaceMainGoal [goal1, goal2]
end Mathlib.Tactic