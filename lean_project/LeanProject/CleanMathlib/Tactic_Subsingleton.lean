import Mathlib.Logic.Basic
open Lean Meta
def Lean.Meta.mkSubsingleton (ty : Expr) : MetaM Expr := do
  let u ← getLevel ty
  return Expr.app (.const ``Subsingleton [u]) ty
def Lean.Meta.synthSubsingletonInst (ty : Expr)
    (insts : Array (Term × AbstractMVarsResult) := #[]) :
    MetaM Expr := do
  withNewMCtxDepth do
    let (insts', uss) ← Array.unzip <$> insts.mapM fun inst => do
      let us ← inst.2.paramNames.mapM fun _ => mkFreshLevelMVar
      pure <| (inst.2.expr.instantiateLevelParamsArray inst.2.paramNames us, us)
    withLocalDeclsD (insts'.map fun e => (`inst, fun _ => inferType e)) fun fvars => do
      withNewLocalInstances fvars 0 do
        let res ← instantiateMVars <| ← synthInstance <| ← mkSubsingleton ty
        let res' := res.abstract fvars
        for i in [0 : fvars.size] do
          if res'.hasLooseBVar (fvars.size - i - 1) then
            uss[i]!.forM fun u => do
              let u ← instantiateLevelMVars u
              if u.isMVar then
                throwErrorAt insts[i]!.1 "\
                  Instance provided to 'subsingleton' has unassigned universe level metavariable\
                  {indentD insts'[i]!}"
          else
            pure ()
        instantiateMVars <| res'.instantiateRev insts'
def Lean.MVarId.subsingleton (g : MVarId) (insts : Array (Term × AbstractMVarsResult) := #[]) :
    MetaM Unit := commitIfNoEx do
  let g ← g.heqOfEq
  g.withContext do
    let tgt ← whnfR (← g.getType)
    if let some (ty, x, y) := tgt.eq? then
      if ← Meta.isProp ty then
        g.assign <| mkApp3 (.const ``proof_irrel []) ty x y
        return
      let u ← getLevel ty
      try
        let inst ← synthSubsingletonInst ty insts
        g.assign <| mkApp4 (.const ``Subsingleton.elim [u]) ty inst x y
        return
      catch _ => pure ()
      let ty' ← whnfR ty
      if ty'.isAppOfArity ``BEq 1 then
        let α := ty'.appArg!
        try
          let some u' := u.dec | failure
          let xInst ← withNewMCtxDepth <| Meta.synthInstance <| mkApp2 (.const ``LawfulBEq [u']) α x
          let yInst ← withNewMCtxDepth <| Meta.synthInstance <| mkApp2 (.const ``LawfulBEq [u']) α y
          g.assign <| mkApp5 (.const ``lawful_beq_subsingleton [u']) α x y xInst yInst
          return
        catch _ => pure ()
      throwError "\
        tactic 'subsingleton' could not prove equality since it could not synthesize\
          {indentD (← mkSubsingleton ty)}"
    else if let some (xTy, x, yTy, y) := tgt.heq? then
      if ← (Meta.isProp xTy <&&> Meta.isProp yTy) then
        g.assign <| mkApp4 (.const ``proof_irrel_heq []) xTy yTy x y
        return
      throwError "tactic 'subsingleton' could not prove heterogeneous equality"
    throwError "tactic 'subsingleton' failed, goal is neither an equality nor a \
      heterogeneous equality"
namespace Mathlib.Tactic
syntax (name := subsingletonStx) "subsingleton" (ppSpace "[" term,* "]")? : tactic
open Elab Tactic
def elabSubsingletonInsts
    (instTerms? : Option (Array Term)) : TermElabM (Array (Term × AbstractMVarsResult)) := do
  if let some instTerms := instTerms? then
    go instTerms.toList #[]
  else
    return #[]
where
  go (instTerms : List Term) (insts : Array (Term × AbstractMVarsResult)) :
      TermElabM (Array (Term × AbstractMVarsResult)) := do
    match instTerms with
    | [] => return insts
    | instTerm :: instTerms =>
      let inst ← withNewMCtxDepth <| Term.withoutModifyingElabMetaStateWithInfo do
        withRef instTerm <| Term.withoutErrToSorry do
          let e ← Term.elabTerm instTerm none
          Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
          let e ← instantiateMVars e
          unless (← isClass? (← inferType e)).isSome do
            throwError "Not an instance. Term has type{indentD <| ← inferType e}"
          if e.hasMVar then
            let r ← abstractMVars e
            let e' ← forallBoundedTelescope (← inferType r.expr) r.numMVars fun args _ => do
              let newBIs ← args.filterMapM fun arg => do
                if (← isClass? (← inferType arg)).isSome then
                  return some (arg.fvarId!, .instImplicit)
                else
                  return none
              withNewBinderInfos newBIs do
                mkLambdaFVars args (r.expr.beta args)
            pure { r with expr := e' }
          else
            pure { paramNames := #[], numMVars := 0, expr := e }
      go instTerms (insts.push (instTerm, inst))
elab_rules : tactic
  | `(tactic| subsingleton $[[$[$instTerms?],*]]?) => withMainContext do
    let recover := (← read).recover
    let insts ← elabSubsingletonInsts instTerms?
    Elab.Tactic.liftMetaTactic1 fun g => do
      let (fvars, g) ← g.intros
      try
        g.subsingleton (insts := insts)
        return none
      catch e =>
        if recover then
          try
            g.refl <|> g.hrefl
            let tac ← if !fvars.isEmpty then `(tactic| (intros; rfl)) else `(tactic| rfl)
            Meta.Tactic.TryThis.addSuggestion (← getRef) tac (origSpan? := ← getRef)
            return none
          catch _ => pure ()
        throw e
end Mathlib.Tactic