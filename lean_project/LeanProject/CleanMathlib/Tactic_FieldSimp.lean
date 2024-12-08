import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Simp.Main
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.NormNum.Core
import Mathlib.Util.DischargerAsTactic
import Qq
namespace Mathlib.Tactic.FieldSimp
open Lean Elab.Tactic Parser.Tactic Lean.Meta
open Qq
initialize registerTraceClass `Tactic.field_simp
private def dischargerTraceMessage {ε : Type*} (prop: Expr) :
    Except ε (Option Expr) → SimpM MessageData
| .error _ | .ok none => return m!"{crossEmoji} discharge {prop}"
| .ok (some _) => return m!"{checkEmoji} discharge {prop}"
open private Simp.dischargeUsingAssumption? from Lean.Meta.Tactic.Simp.Rewrite
partial def discharge (prop : Expr) : SimpM (Option Expr) :=
  withTraceNode `Tactic.field_simp (dischargerTraceMessage prop) do
    if let some r ← Simp.dischargeUsingAssumption? prop then
      return some r
    let prop : Q(Prop) ← (do pure prop)
    let pf? ← match prop with
    | ~q(($e : $α) ≠ $b) =>
        try
          let res ← Mathlib.Meta.NormNum.derive (α := (q(Prop) : Q(Type))) prop
          match res with
          | .isTrue pf => pure (some pf)
          | _ => pure none
        catch _ =>
          pure none
    | _ => pure none
    if let some pf := pf? then return some pf
    let pf? ←
      try some <$> Mathlib.Meta.Positivity.solve prop
      catch _ => pure none
    if let some pf := pf? then return some pf
    Simp.withIncDischargeDepth do
      let ctx ← readThe Simp.Context
      let stats : Simp.Stats := { (← get) with }
      let ⟨simpResult, stats'⟩ ←
        simp prop ctx #[(← Simp.getSimprocs)]
          discharge stats
      set { (← get) with usedTheorems := stats'.usedTheorems, diag := stats'.diag }
      if simpResult.expr.isConstOf ``True then
        try
          return some (← mkOfEqTrue (← simpResult.getProof))
        catch _ =>
          return none
      else
        return none
@[inherit_doc discharge]
elab "field_simp_discharge" : tactic => wrapSimpDischarger Mathlib.Tactic.FieldSimp.discharge
syntax (name := fieldSimp) "field_simp" optConfig (discharger)? (&" only")?
  (simpArgs)? (location)? : tactic
elab_rules : tactic
| `(tactic| field_simp $cfg:optConfig $[(discharger := $dis)]? $[only%$only?]?
    $[$sa:simpArgs]? $[$loc:location]?) => withMainContext do
  let cfg ← elabSimpConfig cfg .simp
  let cfg := { cfg with maxDischargeDepth := max cfg.maxDischargeDepth 7 }
  let loc := expandOptLocation (mkOptionalNode loc)
  let dis ← match dis with
  | none => pure discharge
  | some d => do
    let ⟨_, d⟩ ← tacticToDischarge d
    pure d
  let thms0 ← if only?.isSome then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else do
    let thms0 ← getSimpTheorems
    let thms0 ← thms0.erase (.decl ``one_div)
    let thms0 ← thms0.erase (.decl `mul_eq_zero)
    thms0.erase (.decl ``one_divp)
  let some ext ← getSimpExtension? `field_simps | throwError "field_simps not found"
  let thms ← ext.getTheorems
  let ctx ← Simp.mkContext cfg
    (simpTheorems := #[thms, thms0])
    (congrTheorems := ← getSimpCongrTheorems)
  let mut r ← elabSimpArgs (sa.getD ⟨.missing⟩) ctx (simprocs := {}) (eraseLocal := false) .simp
  if r.starArg then
    r ← do
      let ctx := r.ctx
      let mut simpTheorems := ctx.simpTheorems
      let hs ← getPropHyps
      for h in hs do
        unless simpTheorems.isErased (.fvar h) do
          simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
      let ctx := ctx.setSimpTheorems simpTheorems
      pure { ctx, simprocs := {} }
  _ ← simpLocation r.ctx {} dis loc
end Mathlib.Tactic.FieldSimp