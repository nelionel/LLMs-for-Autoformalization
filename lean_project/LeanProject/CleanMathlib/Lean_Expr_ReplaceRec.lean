import Lean.Expr
import Mathlib.Util.MemoFix
namespace Lean.Expr
def replaceRec (f? : (Expr → Expr) → Expr → Option Expr) : Expr → Expr :=
  memoFix fun r e ↦
    match f? r e with
    | some x => x
    | none   => traverseChildren (M := Id) r e
end Lean.Expr