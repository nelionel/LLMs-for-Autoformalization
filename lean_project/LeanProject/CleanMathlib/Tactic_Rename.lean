import Lean.Elab.Tactic.ElabTerm
import Mathlib.Init
namespace Mathlib.Tactic
open Lean Elab.Tactic Meta
syntax renameArg := term " => " ident
syntax (name := rename') "rename' " renameArg,+ : tactic
elab_rules : tactic
  | `(tactic| rename' $[$as:term => $bs:ident],*) => do
    let ids ← getFVarIds as
    liftMetaTactic1 fun goal ↦ do
      let mut lctx ← getLCtx
      for fvar in ids, tgt in bs do
        lctx := lctx.setUserName fvar tgt.getId
      let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances)
        (← goal.getType) MetavarKind.syntheticOpaque (← goal.getTag)
      goal.assign mvarNew
      pure mvarNew.mvarId!
    withMainContext do
      for fvar in ids, tgt in bs do
        Elab.Term.addTermInfo' tgt (mkFVar fvar)
end Mathlib.Tactic