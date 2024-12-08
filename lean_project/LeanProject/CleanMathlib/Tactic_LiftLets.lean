import Mathlib.Tactic.Basic
open Lean Elab Parser Meta Tactic
structure Lean.Expr.LiftLetsConfig where
  proofs : Bool := false
  merge : Bool := true
private partial def Lean.Expr.liftLetsAux (config : LiftLetsConfig) (e : Expr) (fvars : Array Expr)
    (f : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  if (e.find? Expr.isLet).isNone then
    return ← f fvars e
  if !config.proofs then
    if ← Meta.isProof e then
      return ← f fvars e
  match e with
  | .letE n t v b _ =>
    t.liftLetsAux config fvars fun fvars t' =>
      v.liftLetsAux config fvars fun fvars v' => do
        if config.merge then
          let fvar? ← fvars.findM? (fun fvar => do
            let decl ← fvar.fvarId!.getDecl
            return decl.type == t' && decl.value? == some v')
          if let some fvar' := fvar? then
            return ← (b.instantiate1 fvar').liftLetsAux config fvars f
        withLetDecl n t' v' fun fvar =>
          (b.instantiate1 fvar).liftLetsAux config (fvars.push fvar) f
  | .app x y =>
    x.liftLetsAux config fvars fun fvars x' => y.liftLetsAux config fvars fun fvars y' =>
      f fvars (.app x' y')
  | .proj n idx s =>
    s.liftLetsAux config fvars fun fvars s' => f fvars (.proj n idx s')
  | .lam n t b i =>
    t.liftLetsAux config fvars fun fvars t => do
      let e' ← withLocalDecl n i t fun fvar => do
        (b.instantiate1 fvar).liftLetsAux config fvars fun fvars2 b => do
          let deps ← collectForwardDeps #[fvar] false
          let fvars2 := fvars2[fvars.size:].toArray
          let (fvars2, fvars2') := fvars2.partition deps.contains
          mkLetFVars fvars2' (← mkLambdaFVars #[fvar] (← mkLetFVars fvars2 b))
      insideLets e' fvars fun fvars e'' => f fvars e''
  | .forallE n t b i =>
    t.liftLetsAux config fvars fun fvars t => do
      let e' ← withLocalDecl n i t fun fvar => do
        (b.instantiate1 fvar).liftLetsAux config fvars fun fvars2 b => do
          let deps ← collectForwardDeps #[fvar] false
          let fvars2 := fvars2[fvars.size:].toArray
          let (fvars2, fvars2') := fvars2.partition deps.contains
          mkLetFVars fvars2' (← mkForallFVars #[fvar] (← mkLetFVars fvars2 b))
      insideLets e' fvars fun fvars e'' => f fvars e''
  | .mdata _ e => e.liftLetsAux config fvars f
  | _ => f fvars e
where
  insideLets {α} (e : Expr) (fvars : Array Expr) (f : Array Expr → Expr → MetaM α) : MetaM α := do
    match e with
    | .letE n t v b _ =>
      withLetDecl n t v fun fvar => insideLets (b.instantiate1 fvar) (fvars.push fvar) f
    | _ => f fvars e
def Lean.Expr.liftLets (e : Expr) (f : Array Expr → Expr → MetaM Expr)
    (config : LiftLetsConfig := {}) : MetaM Expr :=
  e.liftLetsAux config #[] f
namespace Mathlib.Tactic
declare_config_elab elabConfig Lean.Expr.LiftLetsConfig
syntax (name := lift_lets) "lift_lets" optConfig (ppSpace location)? : tactic
elab_rules : tactic
  | `(tactic| lift_lets $cfg:optConfig $[$loc:location]?) => do
    let config ← elabConfig (mkOptionalNode cfg)
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h ↦ liftMetaTactic1 fun mvarId ↦ do
        let hTy ← instantiateMVars (← h.getType)
        mvarId.changeLocalDecl h (← hTy.liftLets mkLetFVars config))
      (atTarget := liftMetaTactic1 fun mvarId ↦ do
        let ty ← instantiateMVars (← mvarId.getType)
        mvarId.change (← ty.liftLets mkLetFVars config))
      (failed := fun _ ↦ throwError "lift_lets tactic failed")
end Mathlib.Tactic