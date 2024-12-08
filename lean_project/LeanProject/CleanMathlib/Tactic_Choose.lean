import Mathlib.Util.Tactic
import Mathlib.Logic.Function.Basic
open Lean Meta Elab Tactic
namespace Mathlib.Tactic.Choose
def mk_sometimes (u : Level) (α nonemp p : Expr) :
    List Expr → Expr × Expr → MetaM (Expr × Expr)
| [], (val, spec) => pure (val, spec)
| (e :: ctx), (val, spec) => do
  let (val, spec) ← mk_sometimes u α nonemp p ctx (val, spec)
  let t ← inferType e
  let b ← isProp t
  if b then do
    let val' ← mkLambdaFVars #[e] val
    pure
      (mkApp4 (Expr.const ``Function.sometimes [Level.zero, u]) t α nonemp val',
      mkApp7 (Expr.const ``Function.sometimes_spec [u]) t α nonemp p val' e spec)
  else pure (val, spec)
inductive ElimStatus
  | success
  | failure (ts : List Expr)
def ElimStatus.merge : ElimStatus → ElimStatus → ElimStatus
  | success, _ => success
  | _, success => success
  | failure ts₁, failure ts₂ => failure (ts₁ ++ ts₂)
def mkFreshNameFrom (orig base : Name) : CoreM Name :=
  if orig = `_ then mkFreshUserName base else pure orig
def choose1 (g : MVarId) (nondep : Bool) (h : Option Expr) (data : Name) :
    MetaM (ElimStatus × Expr × MVarId) := do
  let (g, h) ← match h with
  | some e => pure (g, e)
  | none   => do
    let (e, g) ← g.intro1P
    pure (g, .fvar e)
  g.withContext do
    let h ← instantiateMVars h
    let t ← inferType h
    forallTelescopeReducing t fun ctx t ↦ do
      (← withTransparency .all (whnf t)).withApp fun
      | .const ``Exists [u], #[α, p] => do
        let data ← mkFreshNameFrom data ((← p.getBinderName).getD `h)
        let ((neFail : ElimStatus), (nonemp : Option Expr)) ← if nondep then
          let ne := (Expr.const ``Nonempty [u]).app α
          let m ← mkFreshExprMVar ne
          let mut g' := m.mvarId!
          for e in ctx do
            if (← isProof e) then continue
            let ty ← whnf (← inferType e)
            let nety := (Expr.const ``Nonempty [u]).app ty
            let neval := mkApp2 (Expr.const ``Nonempty.intro [u]) ty e
            g' ← g'.assert .anonymous nety neval
          (_, g') ← g'.intros
          g'.withContext do
            match ← synthInstance? (← g'.getType) with
            | some e => do
              g'.assign e
              let m ← instantiateMVars m
              pure (.success, some m)
            | none => pure (.failure [ne], none)
        else pure (.failure [], none)
        let ctx' ← if nonemp.isSome then ctx.filterM (not <$> isProof ·) else pure ctx
        let dataTy ← mkForallFVars ctx' α
        let mut dataVal := mkApp3 (.const ``Classical.choose [u]) α p (mkAppN h ctx)
        let mut specVal := mkApp3 (.const ``Classical.choose_spec [u]) α p (mkAppN h ctx)
        if let some nonemp := nonemp then
          (dataVal, specVal) ← mk_sometimes u α nonemp p ctx.toList (dataVal, specVal)
        dataVal ← mkLambdaFVars ctx' dataVal
        specVal ← mkLambdaFVars ctx specVal
        let (fvar, g) ← withLocalDeclD .anonymous dataTy fun d ↦ do
          let specTy ← mkForallFVars ctx (p.app (mkAppN d ctx')).headBeta
          g.withContext <| withLocalDeclD data dataTy fun d' ↦ do
            let mvarTy ← mkArrow (specTy.replaceFVar d d') (← g.getType)
            let newMVar ← mkFreshExprSyntheticOpaqueMVar mvarTy (← g.getTag)
            g.assign <| mkApp2 (← mkLambdaFVars #[d'] newMVar) dataVal specVal
            pure (d', newMVar.mvarId!)
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (neFail, fvar, g)
      | .const ``And _, #[p, q] => do
        let data ← mkFreshNameFrom data `h
        let e1 ← mkLambdaFVars ctx <| mkApp3 (.const ``And.left  []) p q (mkAppN h ctx)
        let e2 ← mkLambdaFVars ctx <| mkApp3 (.const ``And.right []) p q (mkAppN h ctx)
        let t1 ← inferType e1
        let t2 ← inferType e2
        let (fvar, g) ← (← (← g.assert .anonymous t2 e2).assert data t1 e1).intro1P
        let g ← match h with
        | .fvar v => g.clear v
        | _ => pure g
        return (.success, .fvar fvar, g)
      | _, _ => throwError "expected a term of the shape `∀xs, ∃a, p xs a` or `∀xs, p xs ∧ q xs`"
def choose1WithInfo (g : MVarId) (nondep : Bool) (h : Option Expr) (data : TSyntax ``binderIdent) :
    MetaM (ElimStatus × MVarId) := do
  let n := if let `(binderIdent| $n:ident) := data then n.getId else `_
  let (status, fvar, g) ← choose1 g nondep h n
  g.withContext <| fvar.addLocalVarInfoForBinderIdent data
  pure (status, g)
def elabChoose (nondep : Bool) (h : Option Expr) :
    List (TSyntax ``binderIdent) → ElimStatus → MVarId → MetaM MVarId
  | [], _, _ => throwError "expect list of variables"
  | [n], status, g =>
    match nondep, status with
    | true, .failure tys => do 
      let mut msg := m!"choose!: failed to synthesize any nonempty instances"
      for ty in tys do
        msg := msg ++ m!"{(← mkFreshExprMVar ty).mvarId!}"
      throwError msg
    | _, _ => do
      let (fvar, g) ← match n with
      | `(binderIdent| $n:ident) => g.intro n.getId
      | _ => g.intro1
      g.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent n
      return g
  | n::ns, status, g => do
    let (status', g) ← choose1WithInfo g nondep h n
    elabChoose nondep none ns (status.merge status') g
syntax (name := choose) "choose" "!"? (ppSpace colGt binderIdent)+ (" using " term)? : tactic
elab_rules : tactic
| `(tactic| choose $[!%$b]? $[$ids]* $[using $h]?) => withMainContext do
  let h ← h.mapM (Elab.Tactic.elabTerm · none)
  let g ← elabChoose b.isSome h ids.toList (.failure []) (← getMainGoal)
  replaceMainGoal [g]
@[inherit_doc choose]
syntax "choose!" (ppSpace colGt binderIdent)+ (" using " term)? : tactic
macro_rules
  | `(tactic| choose! $[$ids]* $[using $h]?) => `(tactic| choose ! $[$ids]* $[using $h]?)
end Mathlib.Tactic.Choose