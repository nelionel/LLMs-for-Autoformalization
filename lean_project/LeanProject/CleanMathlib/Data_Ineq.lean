import Mathlib.Lean.Expr.Basic
open Lean Elab Tactic Meta
namespace Mathlib
inductive Ineq : Type
  | eq | le | lt
deriving DecidableEq, Inhabited, Repr
namespace Ineq
def max : Ineq → Ineq → Ineq
  | lt, _ => lt
  | _, lt => lt
  | le, _ => le
  | _, le => le
  | eq, eq => eq
def cmp : Ineq → Ineq → Ordering
  | eq, eq => Ordering.eq
  | eq, _ => Ordering.lt
  | le, le => Ordering.eq
  | le, lt => Ordering.lt
  | lt, lt => Ordering.eq
  | _, _ => Ordering.gt
def toString : Ineq → String
  | eq => "="
  | le => "≤"
  | lt => "<"
instance : ToString Ineq := ⟨toString⟩
instance : ToFormat Ineq := ⟨fun i => Ineq.toString i⟩
end Mathlib.Ineq
namespace Lean.Expr
open Mathlib
def ineq? (e : Expr) : MetaM (Ineq × Expr × Expr × Expr) := do
  let e ← whnfR (← instantiateMVars e)
  match e.eq? with
  | some p => return (Ineq.eq, p)
  | none =>
  match e.le? with
  | some p => return (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => return (Ineq.lt, p)
  | none => throwError "Not a comparison: {e}"
def ineqOrNotIneq? (e : Expr) : MetaM (Bool × Ineq × Expr × Expr × Expr) := do
  try
    return (true, ← e.ineq?)
  catch _ =>
    let some e' := e.not? | throwError "Not a comparison: {e}"
    return (false, ← e'.ineq?)
end Lean.Expr