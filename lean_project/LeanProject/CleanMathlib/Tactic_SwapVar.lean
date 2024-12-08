import Lean.Elab.ElabRules
import Mathlib.Util.Tactic
open Lean Meta Elab.Tactic
namespace Mathlib.Tactic
syntax swapRule := ident " ↔"? ppSpace ident
elab "swap_var " swapRules:(colGt swapRule),+ : tactic => do
  let mvarId ← getMainGoal
  let mdecl ← mvarId.getDecl
  let localInstances := mdecl.localInstances
  let lctx ← swapRules.getElems.foldlM (init := mdecl.lctx) fun lctx swapRule ↦ do
    withLCtx lctx localInstances do
      let `(swapRule| $n₁:ident $[↔]? $n₂:ident) := swapRule
        | unreachable!
      let n₁ := n₁.getId
      let n₂ := n₂.getId
      let fvarId₁ := (← getLocalDeclFromUserName n₁).fvarId
      let fvarId₂ := (← getLocalDeclFromUserName n₂).fvarId
      return lctx.setUserName fvarId₁ n₂ |>.setUserName fvarId₂ n₁
  let mdecl := { mdecl with lctx := lctx }
  modifyMCtx fun mctx ↦ { mctx with decls := mctx.decls.insert mvarId mdecl }
end Mathlib.Tactic