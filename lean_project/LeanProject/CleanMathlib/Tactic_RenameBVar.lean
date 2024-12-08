import Lean.Elab.Tactic.Location
import Mathlib.Util.Tactic
import Mathlib.Lean.Expr.Basic
namespace Mathlib.Tactic
open Lean Parser Elab Tactic
def renameBVarHyp (mvarId : MVarId) (fvarId : FVarId) (old new : Name) :
    MetaM Unit :=
  modifyLocalDecl mvarId fvarId fun ldecl ↦
    ldecl.setType <| ldecl.type.renameBVar old new
def renameBVarTarget (mvarId : MVarId) (old new : Name) : MetaM Unit :=
  modifyTarget mvarId fun e ↦ e.renameBVar old new
elab "rename_bvar " old:ident " → " new:ident loc?:(location)? : tactic => do
  let mvarId ← getMainGoal
  match loc? with
  | none => renameBVarTarget mvarId old.getId new.getId
  | some loc =>
    withLocation (expandLocation loc)
      (fun fvarId ↦ renameBVarHyp mvarId fvarId old.getId new.getId)
      (renameBVarTarget mvarId old.getId new.getId)
      fun _ ↦ throwError "unexpected location syntax"
end Mathlib.Tactic