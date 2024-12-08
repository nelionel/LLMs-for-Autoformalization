import Lean.Elab.Tactic.Simp
import Mathlib.Init
namespace Mathlib.Tactic
open Lean Meta Elab Tactic
partial def simpIntroCore (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[])
    (discharge? : Option Simp.Discharge) (more : Bool) (ids : List (TSyntax ``binderIdent)) :
    TermElabM (Option MVarId) := do
  let done := return (← simpTargetCore g ctx simprocs discharge?).1
  let (transp, var, ids') ← match ids with
    | [] => if more then pure (.reducible, mkHole (← getRef), []) else return ← done
    | v::ids => pure (.default, v.raw[0], ids)
  let t ← withTransparency transp g.getType'
  let n := if var.isIdent then var.getId else `_
  let withFVar := fun (fvar, g) ↦ g.withContext do
    Term.addLocalVarInfo var (mkFVar fvar)
    let simpTheorems ← ctx.simpTheorems.addTheorem (.fvar fvar) (.fvar fvar)
    simpIntroCore g (ctx.setSimpTheorems simpTheorems) simprocs discharge? more ids'
  match t with
  | .letE .. => withFVar (← g.intro n)
  | .forallE (body := body) .. =>
    let (fvar, g) ← g.intro n
    if body.hasLooseBVars then withFVar (fvar, g) else
    match (← simpLocalDecl g fvar ctx simprocs discharge?).1 with
    | none =>
      g.withContext <| Term.addLocalVarInfo var (mkFVar fvar)
      return none
    | some g' => withFVar g'
  | _ =>
    if more && ids.isEmpty then done else
    throwErrorAt var "simp_intro failed to introduce {var}\n{g}"
open Parser.Tactic
elab "simp_intro" cfg:optConfig disch:(discharger)?
    ids:(ppSpace colGt binderIdent)* more:" .."? only:(&" only")? args:(simpArgs)? : tactic => do
  let args := args.map fun args ↦ ⟨args.raw[1].getArgs⟩
  let stx ← `(tactic| simp $cfg:optConfig $(disch)? $[only%$only]? $[[$args,*]]?)
  let { ctx, simprocs, dischargeWrapper } ←
    withMainContext <| mkSimpContext stx (eraseLocal := false)
  dischargeWrapper.with fun discharge? ↦ do
    let g ← getMainGoal
    g.checkNotAssigned `simp_intro
    g.withContext do
      let g? ← simpIntroCore g ctx (simprocs := simprocs) discharge? more.isSome ids.toList
      replaceMainGoal <| if let some g := g? then [g] else []
end Mathlib.Tactic