import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
open Lean.Meta
namespace Lean.Elab.Tactic
syntax (name := clearExcept) "clear " "*" " -" (ppSpace colGt ident)* : tactic
elab_rules : tactic
  | `(tactic| clear * - $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal ↦ do
      let mut toClear : Array FVarId := #[]
      for decl in ← getLCtx do
        unless fvarIds.contains decl.fvarId do
          if let none ← isClass? decl.type then
            toClear := toClear.push decl.fvarId
      goal.tryClearMany toClear
end Lean.Elab.Tactic