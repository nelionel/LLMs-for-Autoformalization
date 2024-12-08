import Lean.Elab.Tactic.ElabTerm
import Mathlib.Tactic.TypeStar
open Lean.Meta
namespace Lean.Elab.Tactic
noncomputable def nonempty_to_inhabited (α : Sort*) (_ : Nonempty α) : Inhabited α :=
  Inhabited.mk (Classical.ofNonempty)
def nonempty_prop_to_inhabited (α : Prop) (α_nonempty : Nonempty α) : Inhabited α :=
  Inhabited.mk <| Nonempty.elim α_nonempty id
syntax (name := inhabit) "inhabit " atomic(ident " : ")? term : tactic
def evalInhabit (goal : MVarId) (h_name : Option Ident) (term : Syntax) : TacticM MVarId := do
  goal.withContext do
    let e ← Tactic.elabTerm term none
    let e_lvl ← Meta.getLevel e
    let inhabited_e := mkApp (mkConst ``Inhabited [e_lvl]) e
    let nonempty_e := mkApp (mkConst ``Nonempty [e_lvl]) e
    let nonempty_e_pf ← synthInstance nonempty_e
    let h_name : Name :=
      match h_name with
      | some h_name => h_name.getId
      | none => `inhabited_h
    let pf ←
      if ← isProp e then Meta.mkAppM ``nonempty_prop_to_inhabited #[e, nonempty_e_pf]
      else Meta.mkAppM ``nonempty_to_inhabited #[e, nonempty_e_pf]
    let (_, r) ← (← goal.assert h_name inhabited_e pf).intro1P
    return r
elab_rules : tactic
  | `(tactic| inhabit $[$h_name:ident :]? $term) => do
    let goal ← evalInhabit (← getMainGoal) h_name term
    replaceMainGoal [goal]
end Lean.Elab.Tactic