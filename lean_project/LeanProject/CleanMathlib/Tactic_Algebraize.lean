import Mathlib.Algebra.Algebra.Tower
open Lean Elab Tactic Term Meta
namespace Lean.Attr
def algebraizeGetParam (thm : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| algebraize $name:ident) => return name.getId
  | `(attr| algebraize) =>
    match thm with
    | .str `RingHom t => return .str `Algebra t
    | _ =>
      throwError "theorem name must be of the form `RingHom.Property` if no argument is provided"
  | _ => throwError "unexpected algebraize argument"
initialize algebraizeAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `algebraize,
    descr :=
"Tag that lets the `algebraize` tactic know which `Algebra` property corresponds to this `RingHom`
property.",
    getParam := algebraizeGetParam }
end Lean.Attr
namespace Mathlib.Tactic
namespace Algebraize
def addAlgebraInstanceFromRingHom (f ft : Expr) : TacticM Unit := withMainContext do
  let (_, l) := ft.getAppFnArgs
  let alg ← mkAppOptM ``Algebra #[l[0]!, l[1]!, none, none]
  unless (← synthInstance? alg).isSome do
  liftMetaTactic fun mvarid => do
    let nm ← mkFreshBinderNameForTactic `algInst
    let mvar ← mvarid.define nm alg (← mkAppM ``RingHom.toAlgebra #[f])
    let (_, mvar) ← mvar.intro1P
    return [mvar]
def addIsScalarTowerInstanceFromRingHomComp (fn : Expr) : TacticM Unit := withMainContext do
  let (_, l) := fn.getAppFnArgs
  let tower ← mkAppOptM ``IsScalarTower #[l[0]!, l[1]!, l[2]!, none, none, none]
  unless (← synthInstance? tower).isSome do
  liftMetaTactic fun mvarid => do
    let nm ← mkFreshBinderNameForTactic `scalarTowerInst
    let h ← mkFreshExprMVar (← mkAppM ``Eq #[
      ← mkAppOptM ``algebraMap #[l[0]!, l[2]!, none, none, none],
      ← mkAppM ``RingHom.comp #[
        ← mkAppOptM ``algebraMap #[l[1]!, l[2]!, none, none, none],
        ← mkAppOptM ``algebraMap #[l[0]!, l[1]!, none, none, none]]])
    h.mvarId!.refl
    let val ← mkAppOptM ``IsScalarTower.of_algebraMap_eq'
      #[l[0]!, l[1]!, l[2]!, none, none, none, none, none, none, h]
    let mvar ← mvarid.define nm tower val
    let (_, mvar) ← mvar.intro1P
    return [mvar]
def addProperties (t : Array Expr) : TacticM Unit := withMainContext do
  let ctx ← getLCtx
  ctx.forM fun decl => do
    if decl.isImplementationDetail then return
    let (nm, args) := decl.type.getAppFnArgs
    match Attr.algebraizeAttr.getParam? (← getEnv) nm with
    | some p =>
      let f := args[args.size - 1]!
      if ¬ (← t.anyM (Meta.isDefEq · f)) then return
      let cinfo ← getConstInfo p
      let n ← getExpectedNumArgs cinfo.type
      let pargs := Array.mkArray n (none : Option Expr)
      if cinfo.isInductive then
        let pargs := pargs.set! 0 args[0]!
        let pargs := pargs.set! 1 args[1]!
        let tp ← mkAppOptM p pargs 
        unless (← synthInstance? tp).isSome do
        liftMetaTactic fun mvarid => do
          let nm ← mkFreshBinderNameForTactic `algebraizeInst
          let (_, mvar) ← mvarid.note nm decl.toExpr tp
          return [mvar]
      else
        let pargs := pargs.set! (n - 1) decl.toExpr
        let val ← mkAppOptM p pargs
        let tp ← inferType val
        unless (← synthInstance? tp).isSome do
        liftMetaTactic fun mvarid => do
          let nm ← mkFreshBinderNameForTactic `algebraizeInst
          let (_, mvar) ← mvarid.note nm val
          return [mvar]
    | none => return
structure Config where
  properties : Bool := true
deriving Inhabited
declare_config_elab elabAlgebraizeConfig Algebraize.Config
end Algebraize
open Algebraize Lean.Parser.Tactic
syntax algebraizeTermSeq := " [" withoutPosition(term,*,?) "]"
syntax "algebraize " optConfig (algebraizeTermSeq)? : tactic
elab_rules : tactic
  | `(tactic| algebraize $cfg:optConfig $args) => withMainContext do
    let cfg ← elabAlgebraizeConfig cfg
    let t ← match args with
    | `(algebraizeTermSeq| [$rs,*]) => rs.getElems.mapM fun i => Term.elabTerm i none
    | _ =>
      throwError ""
    if t.size == 0 then
      logWarningAt args "`algebraize []` without arguments has no effect!"
    for f in t do
      let ft ← inferType f
      match ft.getAppFn with
      | Expr.const ``RingHom _ => addAlgebraInstanceFromRingHom f ft
      | _ => throwError m!"{f} is not of type `RingHom`"
    for f in t do
      match f.getAppFn with
      | Expr.const ``RingHom.comp _ =>
        try addIsScalarTowerInstanceFromRingHomComp f
        catch _ => continue
      | _ => continue
    if cfg.properties then
      addProperties t
  | `(tactic| algebraize $[$config]?) => do
    throwError "`algebraize` expects a list of arguments: `algebraize [f]`"
syntax "algebraize_only" (ppSpace algebraizeTermSeq)? : tactic
macro_rules
  | `(tactic| algebraize_only $[$args]?) =>
    `(tactic| algebraize -properties $[$args]?)
end Mathlib.Tactic