import Mathlib.Init
import Batteries.Data.Rat.Basic
import Batteries.Tactic.Alias
namespace Lean.Expr
def rat? (e : Expr) : Option Rat := do
  if e.isAppOfArity ``Div.div 4 then
    let d ← e.appArg!.nat?
    guard (d ≠ 1)
    let n ← e.appFn!.appArg!.int?
    let q := mkRat n d
    guard (q.den = d)
    pure q
  else
    e.int?
def isExplicitNumber : Expr → Bool
  | .lit _ => true
  | .mdata _ e => isExplicitNumber e
  | e => e.rat?.isSome
end Lean.Expr