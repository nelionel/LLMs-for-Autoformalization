import Lean.Elab.Tactic.Config
import Lean.Elab.Tactic.RCases
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Rfl
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Logic.Basic
universe u v
open Lean Meta Elab Tactic
initialize registerTraceClass `congr!
initialize registerTraceClass `congr!.synthesize
structure Congr!.Config where
  closePre : Bool := true
  closePost : Bool := true
  transparency : TransparencyMode := TransparencyMode.reducible
  preTransparency : TransparencyMode := TransparencyMode.reducible
  preferLHS : Bool := true
  partialApp : Bool := true
  sameFun : Bool := false
  maxArgs : Option Nat := none
  typeEqs : Bool := false
  etaExpand : Bool := false
  useCongrSimp : Bool := false
  beqEq : Bool := true
def Congr!.Config.unfoldSameFun : Congr!.Config where
  partialApp := false
  sameFun := true
  transparency := .default
  preTransparency := .default
def Congr!.Config.numArgsOk (config : Config) (numArgs : Nat) : Bool :=
  numArgs ≤ config.maxArgs.getD numArgs
def Congr!.Config.maxArgsFor (config : Config) (numArgs : Nat) : Nat :=
  min numArgs (config.maxArgs.getD numArgs)
private def applyCongrThm?
    (config : Congr!.Config) (mvarId : MVarId) (congrThmType congrThmProof : Expr) :
    MetaM (List MVarId) := do
  trace[congr!] "trying to apply congr lemma {congrThmType}"
  try
    let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThmType congrThmProof
    let (fvarId, mvarId) ← mvarId.intro1P
    let mvarIds ← withTransparency config.transparency <|
      mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
    mvarIds.mapM fun mvarId => mvarId.tryClear fvarId
  catch e =>
    withTraceNode `congr! (fun _ => pure m!"failed to apply congr lemma") do
      trace[congr!] "{e.toMessageData}"
    throw e
def Congr!.plausiblyEqualTypes (ty1 ty2 : Expr) (maxDepth : Nat := 5) : MetaM Bool :=
  match maxDepth with
  | 0 => return false
  | maxDepth + 1 => do
    if (← isProp ty1) && (← isProp ty2) then
      return true
    unless ← withNewMCtxDepth <| isDefEq (← inferType ty1) (← inferType ty2) do
      return false
    let ty1 ← whnfD ty1
    let ty2 ← whnfD ty2
    unless ← withNewMCtxDepth <| isDefEq ty1.getAppFn ty2.getAppFn do
      return false
    for arg1 in ty1.getAppArgs, arg2 in ty2.getAppArgs do
      if (← isType arg1) && (← isType arg2) then
        unless ← plausiblyEqualTypes arg1 arg2 maxDepth do
          return false
    return true
partial
def Lean.MVarId.smartHCongr? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congr!
    commitWhenSome? do
      let mvarId ← mvarId.eqOfHEq
      let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | return none
      if let some mvars ← loop mvarId 0 lhs rhs [] [] then
        return mvars
      trace[congr!] "Default smartHCongr? failed, trying LHS/RHS method"
      let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
      if let some mvars ← forSide mvarId fst then
        return mvars
      else if let some mvars ← forSide mvarId snd then
        return mvars
      else
        return none
where
  loop (mvarId : MVarId) (numArgs : Nat) (lhs rhs : Expr) (lhsArgs rhsArgs : List Expr) :
      MetaM (Option (List MVarId)) :=
    match lhs.cleanupAnnotations, rhs.cleanupAnnotations with
    | .app f a, .app f' b => do
      if not (config.numArgsOk (numArgs + 1)) then
        return none
      let lhsArgs' := a :: lhsArgs
      let rhsArgs' := b :: rhsArgs
      if let some mvars ← loop mvarId (numArgs + 1) f f' lhsArgs' rhsArgs' then
        return mvars
      if not config.partialApp && f.isApp && f'.isApp then
        return none
      unless ← withNewMCtxDepth <| isDefEq (← inferType f) (← inferType f') do
        return none
      let funDefEq ← withReducible <| withNewMCtxDepth <| isDefEq f f'
      if config.sameFun && not funDefEq then
        return none
      let info ← getFunInfoNArgs f (numArgs + 1)
      let mut fixed : Array Bool := #[]
      for larg in lhsArgs', rarg in rhsArgs', pinfo in info.paramInfo do
        if !config.typeEqs && (!pinfo.isExplicit || pinfo.hasFwdDeps) then
          if ← isType larg then
            unless ← Congr!.plausiblyEqualTypes larg rarg do
              fixed := fixed.push true
              continue
        fixed := fixed.push (← withReducible <| withNewMCtxDepth <| isDefEq larg rarg)
      let cthm ← mkRichHCongr (forceHEq := true) (← inferType f) info
                  (fixedFun := funDefEq) (fixedParams := fixed)
      let (congrThm', congrProof') :=
        if funDefEq then
          (cthm.type.bindingBody!.instantiate1 f, cthm.proof.beta #[f])
        else
          (cthm.type.bindingBody!.bindingBody!.instantiateRev #[f, f'],
           cthm.proof.beta #[f, f'])
      observing? <| applyCongrThm? config mvarId congrThm' congrProof'
    | _, _ => return none
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) := do
    let side := side.cleanupAnnotations
    if not side.isApp then return none
    let numArgs := config.maxArgsFor side.getAppNumArgs
    if not config.partialApp && numArgs < side.getAppNumArgs then
        return none
    let mut f := side
    for _ in [:numArgs] do
      f := f.appFn!'
    let info ← getFunInfoNArgs f numArgs
    let mut fixed : Array Bool := #[]
    if !config.typeEqs then
      for pinfo in info.paramInfo, arg in side.getAppArgs do
        if pinfo.isProp || !(← isType arg) then
          fixed := fixed.push false
        else if pinfo.isExplicit && !pinfo.hasFwdDeps then
          fixed := fixed.push false
        else
          fixed := fixed.push true
    let cthm ← mkRichHCongr (forceHEq := true) (← inferType f) info
                (fixedFun := true) (fixedParams := fixed)
    let congrThm' := cthm.type.bindingBody!.instantiate1 f
    let congrProof' := cthm.proof.beta #[f]
    observing? <| applyCongrThm? config mvarId congrThm' congrProof'
def Lean.MVarId.congrSimp? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congrSimp?
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide mvarId fst then
      return mvars
    else if let some mvars ← forSide mvarId snd then
      return mvars
    else
      return none
where
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) :=
    commitWhenSome? do
      let side := side.cleanupAnnotations
      if not side.isApp then return none
      let numArgs := config.maxArgsFor side.getAppNumArgs
      if not config.partialApp && numArgs < side.getAppNumArgs then
        return none
      let mut f := side
      for _ in [:numArgs] do
        f := f.appFn!'
      let some congrThm ← mkCongrSimpNArgs f numArgs
        | return none
      observing? <| applyCongrThm? config mvarId congrThm.type congrThm.proof
  mkCongrSimpNArgs (f : Expr) (nArgs : Nat) : MetaM (Option CongrTheorem) := do
    let f := (← Lean.instantiateMVars f).cleanupAnnotations
    let info ← getFunInfoNArgs f nArgs
    mkCongrSimpCore? f info
      (← getCongrSimpKinds f info) (subsingletonInstImplicitRhs := false)
def Lean.MVarId.userCongr? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `userCongr?
    let some (lhs, rhs) := (← withReducible mvarId.getType').eqOrIff? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide fst then
      return mvars
    else if let some mvars ← forSide snd then
      return mvars
    else
      return none
where
  forSide (side : Expr) : MetaM (Option (List MVarId)) := do
    let side := side.cleanupAnnotations
    if not side.isApp then return none
    let some name := side.getAppFn.constName? | return none
    let congrTheorems := (← getSimpCongrTheorems).get name
    for congrTheorem in congrTheorems do
      let res ← observing? do
        let cinfo ← getConstInfo congrTheorem.theoremName
        let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let proof := mkConst congrTheorem.theoremName us
        let ptype ← instantiateTypeLevelParams cinfo us
        applyCongrThm? config mvarId ptype proof
      if let some mvars := res then
        return mvars
    return none
def Lean.MVarId.congrPi? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do withReducible <| mvarId.apply (← mkConstWithFreshMVarLevels `pi_congr)
def Lean.MVarId.obviousFunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext <| observing? do
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels ``funext)
def Lean.MVarId.obviousHfunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext <| observing? do
    let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels `Function.hfunext)
private theorem implies_congr' {α α' : Sort u} {β β' : Sort v} (h : α = α') (h' : α' → β = β') :
    (α → β) = (α' → β') := by
  cases h
  show (∀ (x : α), (fun _ => β) x) = _
  rw [funext h']
def Lean.MVarId.congrImplies?' (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do
    let [mvarId₁, mvarId₂] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr')
      | throwError "unexpected number of goals"
    return [mvarId₁, mvarId₂]
protected theorem FastSubsingleton.helim {α β : Sort u} [FastSubsingleton α]
    (h₂ : α = β) (a : α) (b : β) : HEq a b := by
  have : Subsingleton α := FastSubsingleton.inst
  exact Subsingleton.helim h₂ a b
def Lean.MVarId.subsingletonHelim? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext <| observing? do
    mvarId.checkNotAssigned `subsingletonHelim
    let some (α, lhs, β, rhs) := (← withReducible mvarId.getType').heq? | failure
    withSubsingletonAsFast fun elim => do
      let eqmvar ← mkFreshExprSyntheticOpaqueMVar (← mkEq α β) (← mvarId.getTag)
      if let some pf ← observing? (mkAppM ``FastSubsingleton.helim #[eqmvar, lhs, rhs]) then
        mvarId.assign <| elim pf
        return [eqmvar.mvarId!]
      let eqsymm ← mkAppM ``Eq.symm #[eqmvar]
      if let some pf ← observing? (mkAppM ``FastSubsingleton.helim #[eqsymm, rhs, lhs]) then
        mvarId.assign <| elim (← mkAppM ``HEq.symm #[pf])
        return [eqmvar.mvarId!]
      failure
def Lean.MVarId.beqInst? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do withReducible <| mvarId.applyConst ``lawful_beq_subsingleton
def Lean.MVarId.congrPasses! :
    List (String × (Congr!.Config → MVarId → MetaM (Option (List MVarId)))) :=
  [("user congr", userCongr?),
   ("hcongr lemma", smartHCongr?),
   ("congr simp lemma", when (·.useCongrSimp) congrSimp?),
   ("Subsingleton.helim", fun _ => subsingletonHelim?),
   ("BEq instances", when (·.beqEq) fun _ => beqInst?),
   ("obvious funext", fun _ => obviousFunext?),
   ("obvious hfunext", fun _ => obviousHfunext?),
   ("congr_implies", fun _ => congrImplies?'),
   ("congr_pi", fun _ => congrPi?)]
where
  when (b : Congr!.Config → Bool) (f : Congr!.Config → MVarId → MetaM (Option (List MVarId)))
      (config : Congr!.Config) (mvar : MVarId) : MetaM (Option (List MVarId)) := do
    unless b config do return none
    f config mvar
structure CongrState where
  goals : Array MVarId
  patterns : List (TSyntax `rcasesPat)
abbrev CongrMetaM := StateRefT CongrState MetaM
def CongrMetaM.nextPattern : CongrMetaM (Option (TSyntax `rcasesPat)) := do
  modifyGet fun s =>
    if let p :: ps := s.patterns then
      (p, {s with patterns := ps})
    else
      (none, s)
private theorem heq_imp_of_eq_imp {α : Sort*} {x y : α} {p : HEq x y → Prop}
    (h : (he : x = y) → p (heq_of_eq he)) (he : HEq x y) : p he := by
  cases he
  exact h rfl
private theorem eq_imp_of_iff_imp {x y : Prop} {p : x = y → Prop}
    (h : (he : x ↔ y) → p (propext he)) (he : x = y) : p he := by
  cases he
  exact h Iff.rfl
partial
def Lean.MVarId.introsClean (mvarId : MVarId) : CongrMetaM (List MVarId) :=
  loop mvarId
where
  heqImpOfEqImp (mvarId : MVarId) : MetaM (Option MVarId) :=
    observing? <| withReducible do
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``heq_imp_of_eq_imp) | failure
      return mvarId
  eqImpOfIffImp (mvarId : MVarId) : MetaM (Option MVarId) :=
    observing? <| withReducible do
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``eq_imp_of_iff_imp) | failure
      return mvarId
  loop (mvarId : MVarId) : CongrMetaM (List MVarId) :=
    mvarId.withContext do
      let ty ← withReducible <| mvarId.getType'
      if ty.isForall then
        let mvarId := (← heqImpOfEqImp mvarId).getD mvarId
        let mvarId := (← eqImpOfIffImp mvarId).getD mvarId
        let ty ← withReducible <| mvarId.getType'
        if ty.isArrow then
          if ← (isTrivialType ty.bindingDomain!
                <||> (← getLCtx).anyM (fun decl => do
                        return (← Lean.instantiateMVars decl.type) == ty.bindingDomain!)) then
            let mvar ← mkFreshExprSyntheticOpaqueMVar ty.bindingBody! (← mvarId.getTag)
            mvarId.assign <| .lam .anonymous ty.bindingDomain! mvar .default
            return ← loop mvar.mvarId!
        if let some patt ← CongrMetaM.nextPattern then
          let gs ← Term.TermElabM.run' <| Lean.Elab.Tactic.RCases.rintro #[patt] none mvarId
          List.flatten <$> gs.mapM loop
        else
          let (_, mvarId) ← mvarId.intro1
          loop mvarId
      else
        return [mvarId]
  isTrivialType (ty : Expr) : MetaM Bool := do
    unless ← Meta.isProp ty do
      return false
    let ty ← Lean.instantiateMVars ty
    if let some (lhs, rhs) := ty.eqOrIff? then
      if lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    if let some (α, lhs, β, rhs) := ty.heq? then
      if α.cleanupAnnotations == β.cleanupAnnotations
          && lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    return false
def Lean.MVarId.preCongr! (mvarId : MVarId) (tryClose : Bool) : MetaM (Option MVarId) := do
  let mvarId ← mvarId.heqOfEq
  if tryClose then
    if ← mvarId.assumptionCore then return none
  let mvarId ← mvarId.iffOfEq
  if tryClose then
    try withAssignableSyntheticOpaque mvarId.refl; return none catch _ => pure ()
    if ← Lean.Meta.fastSubsingletonElim mvarId then return none
    if ← mvarId.proofIrrelHeq then return none
  return some mvarId
def Lean.MVarId.congrCore! (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  mvarId.checkNotAssigned `congr!
  let s ← saveState
  let mvarId ← mvarId.liftReflToEq
  for (passName, pass) in congrPasses! do
    try
      if let some mvarIds ← pass config mvarId then
        trace[congr!] "pass succeeded: {passName}"
        return mvarIds
    catch e =>
      throwTacticEx `congr! mvarId
        m!"internal error in congruence pass {passName}, {e.toMessageData}"
    if ← mvarId.isAssigned then
      throwTacticEx `congr! mvarId
        s!"congruence pass {passName} assigned metavariable but failed"
  restoreState s
  trace[congr!] "no passes succeeded"
  return none
def Lean.MVarId.postCongr! (config : Congr!.Config) (mvarId : MVarId) : MetaM (Option MVarId) := do
  let some mvarId ← mvarId.preCongr! config.closePost | return none
  let mvarId ← mvarId.propext
  if config.closePost then
    if ← mvarId.assumptionCore then return none
  if config.etaExpand then
    if let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? then
      let lhs' ← Meta.etaExpand lhs
      let rhs' ← Meta.etaExpand rhs
      return ← mvarId.change (← mkEq lhs' rhs')
  return mvarId
def Lean.MVarId.congrN! (mvarId : MVarId)
    (depth? : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rcasesPat) := []) :
    MetaM (List MVarId) := do
  let ty ← withReducible <| mvarId.getType'
  let defaultDepth := min 1000000 (8 * (1 + ty.approxDepth.toNat))
  let depth := depth?.getD defaultDepth
  let (_, s) ← go depth depth mvarId |>.run {goals := #[], patterns := patterns}
  return s.goals.toList
where
  post (mvarId : MVarId) : CongrMetaM Unit := do
    for mvarId in ← mvarId.introsClean do
      if let some mvarId ← mvarId.postCongr! config then
        modify (fun s => {s with goals := s.goals.push mvarId})
      else
        trace[congr!] "Dispatched goal by post-processing step."
  go (depth : Nat) (n : Nat) (mvarId : MVarId) : CongrMetaM Unit := do
    for mvarId in ← mvarId.introsClean do
      if let some mvarId ← withTransparency config.preTransparency <|
                              mvarId.preCongr! config.closePre then
        match n with
          | 0 =>
            trace[congr!] "At level {depth - n}, doing post-processing. {mvarId}"
            post mvarId
          | n + 1 =>
            trace[congr!] "At level {depth - n}, trying congrCore!. {mvarId}"
            if let some mvarIds ← mvarId.congrCore! config then
              mvarIds.forM (go depth n)
            else
              post mvarId
namespace Congr!
declare_config_elab elabConfig Config
syntax (name := congr!) "congr!" Parser.Tactic.optConfig (ppSpace num)?
  (" with" (ppSpace colGt rintroPat)*)? : tactic
elab_rules : tactic
| `(tactic| congr! $cfg:optConfig $[$n]? $[with $ps?*]?) => do
  let config ← elabConfig cfg
  let patterns := (Lean.Elab.Tactic.RCases.expandRIntroPats (ps?.getD #[])).toList
  liftMetaTactic fun g ↦
    let depth := n.map (·.getNat)
    g.congrN! depth config patterns
end Congr!