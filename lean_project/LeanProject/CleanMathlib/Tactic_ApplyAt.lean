import Lean.Elab.Tactic.ElabTerm
import Mathlib.Lean.Meta.Basic
open Lean Meta Elab Tactic Term
namespace Mathlib.Tactic
elab "apply" t:term "at" i:ident : tactic => withSynthesize <| withMainContext do
  let f ← elabTermForApply t
  let some ldecl := (← getLCtx).findFromUserName? i.getId
    | throwErrorAt i m!"Identifier {i} not found"
  let (mvs, bis, tp) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  for (m, b) in mvs.zip bis do
    if b.isInstImplicit && !(← m.mvarId!.isAssigned) then
      try m.mvarId!.inferInstance
      catch _ => continue
  let mainGoal ← mainGoal.assert ldecl.userName tp
    (← mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map fun e => some e))
  let (_, mainGoal) ← mainGoal.intro1P
  replaceMainGoal <| [mainGoal] ++ mvs.pop.toList.map fun e => e.mvarId!
end Mathlib.Tactic