import Mathlib.Init
import Lean.PrettyPrinter.Delaborator.Basic
namespace Lean.PrettyPrinter.Delaborator
open Lean.Meta Lean.SubExpr SubExpr
def withBindingBodyUnusedName' {α} (d : Syntax → Expr → DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  withBindingBody' n (fun fvar => return (← mkAnnotatedIdent n fvar, fvar))
    (fun (stxN, fvar) => d stxN fvar)
def OptionsPerPos.setBool (opts : OptionsPerPos) (p : SubExpr.Pos) (n : Name) (v : Bool) :
    OptionsPerPos :=
  let e := opts.findD p {} |>.setBool n v
  opts.insert p e
end Lean.PrettyPrinter.Delaborator