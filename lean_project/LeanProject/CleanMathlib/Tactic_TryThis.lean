import Mathlib.Init
import Lean.Meta.Tactic.TryThis
namespace Mathlib.Tactic
open Lean
elab tk:"try_this" tac:tactic : tactic => do
  Elab.Tactic.evalTactic tac
  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)
elab tk:"try_this" tac:conv : conv => do
  Elab.Tactic.evalTactic tac
  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)
end Mathlib.Tactic