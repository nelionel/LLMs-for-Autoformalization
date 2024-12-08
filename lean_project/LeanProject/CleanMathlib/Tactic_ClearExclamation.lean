import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
namespace Mathlib.Tactic
open Lean Meta Elab.Tactic
elab (name := clear!) "clear!" hs:(ppSpace colGt ident)* : tactic => do
  let fvarIds ← getFVarIds hs
  liftMetaTactic1 fun goal ↦ do
    goal.tryClearMany <| (← collectForwardDeps (fvarIds.map .fvar) true).map (·.fvarId!)
end Mathlib.Tactic