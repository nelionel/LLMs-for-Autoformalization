import Lean
import Batteries.Lean.Except
import Batteries.Tactic.Exact
import Mathlib.Tactic.Core
import Mathlib.Tactic.GCongr.ForwardAttr
import Mathlib.Order.Defs.PartialOrder
namespace Mathlib.Tactic.GCongr
open Lean Meta
structure GCongrLemma where
  declName : Name
  mainSubgoals : Array (Nat × Nat)
  varyingArgs : Array Bool
  deriving Inhabited, Repr
initialize gcongrExt : SimpleScopedEnvExtension ((Name × Name × Array Bool) × GCongrLemma)
    (Std.HashMap (Name × Name × Array Bool) (Array GCongrLemma)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, lem) => m.insert n ((m.getD n #[]).push lem)
    initial := {}
  }
initialize registerBuiltinAttribute {
  name := `gcongr
  descr := "generalized congruence"
  add := fun decl _ kind ↦ MetaM.run' do
    let declTy := (← getConstInfo decl).type
    withReducible <| forallTelescopeReducing declTy fun xs targetTy => do
    let fail (m : MessageData) := throwError "\
      @[gcongr] attribute only applies to lemmas proving f x₁ ... xₙ ∼ f x₁' ... xₙ'.\n \
      {m} in the conclusion of {declTy}"
    let .app (.app rel lhs) rhs ← whnf targetTy |
      fail "No relation with at least two arguments found"
    let some relName := rel.getAppFn.constName? | fail "No relation found"
    let (some head, lhsArgs) := lhs.withApp fun e a => (e.constName?, a) |
      fail "LHS is not a function"
    let (some head', rhsArgs) := rhs.withApp fun e a => (e.constName?, a) |
      fail "RHS is not a function"
    unless head == head' && lhsArgs.size == rhsArgs.size do
      fail "LHS and RHS do not have the same head function and arity"
    let mut varyingArgs := #[]
    let mut pairs := #[]
    for e1 in lhsArgs, e2 in rhsArgs do
      let isEq := (← isDefEq e1 e2) || ((← isProof e1) && (← isProof e2))
      if !isEq then
        let e1 := e1.eta
        let e2 := e2.eta
        unless e1.isFVar && e2.isFVar do fail "Not all arguments are free variables"
        pairs := pairs.push (varyingArgs.size, e1, e2)
      varyingArgs := varyingArgs.push !isEq
    let mut mainSubgoals := #[]
    let mut i := 0
    for hyp in xs do
      mainSubgoals ← forallTelescopeReducing (← inferType hyp) fun _args hypTy => do
        let mut mainSubgoals := mainSubgoals
        if let .app (.app _ lhs₁) rhs₁ ← whnf hypTy then
          let lhs₁ := lhs₁.getAppFn
          let rhs₁ := rhs₁.getAppFn
          if let some j ← pairs.findM? fun (_, e1, e2) =>
            isDefEq lhs₁ e1 <&&> isDefEq rhs₁ e2 <||>
            isDefEq lhs₁ e2 <&&> isDefEq rhs₁ e1
          then
            mainSubgoals := mainSubgoals.push (i, j.1)
        pure mainSubgoals
      i := i + 1
    gcongrExt.add
      ((relName, head, varyingArgs), { declName := decl, mainSubgoals, varyingArgs }) kind
}
initialize registerTraceClass `Meta.gcongr
syntax "gcongr_discharger" : tactic
def gcongrDischarger (goal : MVarId) : MetaM Unit := Elab.Term.TermElabM.run' do
  trace[Meta.gcongr] "Attempting to discharge side goal {goal}"
  let [] ← Elab.Tactic.run goal <|
      Elab.Tactic.evalTactic (Unhygienic.run `(tactic| gcongr_discharger))
    | failure
open Elab Tactic
@[gcongr_forward] def exactRefl : ForwardExt where
  eval h goal := do
    let m ← mkFreshExprMVar none
    goal.assignIfDefeq (← mkAppOptM ``Eq.subst #[h, m])
    goal.applyRfl
@[gcongr_forward] def exactLeOfLt : ForwardExt where
  eval h goal := do goal.assignIfDefeq (← mkAppM ``le_of_lt #[h])
@[gcongr_forward] def symmExact : ForwardExt where
  eval h goal := do (← goal.applySymm).assignIfDefeq h
@[gcongr_forward] def exact : ForwardExt where
  eval e m := m.assignIfDefeq e
def _root_.Lean.MVarId.gcongrForward (hs : Array Expr) (g : MVarId) : MetaM Unit :=
  withReducible do
    let s ← saveState
    withTraceNode `Meta.gcongr (fun _ => return m!"gcongr_forward: ⊢ {← g.getType}") do
    let tacs := (forwardExt.getState (← getEnv)).2
    for h in hs do
      try
        tacs.firstM fun (n, tac) =>
          withTraceNode `Meta.gcongr (return m!"{·.emoji} trying {n} on {h} : {← inferType h}") do
            tac.eval h g
        return
      catch _ => s.restore
    throwError "gcongr_forward failed"
def gcongrForwardDischarger (goal : MVarId) : MetaM Unit := Elab.Term.TermElabM.run' do
  let mut hs := #[]
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      hs := hs.push (.fvar h.fvarId)
  goal.gcongrForward hs
partial def _root_.Lean.MVarId.gcongr
    (g : MVarId) (template : Option Expr) (names : List (TSyntax ``binderIdent))
    (mainGoalDischarger : MVarId → MetaM Unit := gcongrForwardDischarger)
    (sideGoalDischarger : MVarId → MetaM Unit := gcongrDischarger) :
    MetaM (Bool × List (TSyntax ``binderIdent) × Array MVarId) := g.withContext do
  withTraceNode `Meta.gcongr (fun _ => return m!"gcongr: ⊢ {← g.getType}") do
  match template with
  | none =>
    try mainGoalDischarger g; return (true, names, #[])
    catch _ => pure ()
  | some tpl =>
    if let .mvar mvarId := tpl.getAppFn then
      if let .syntheticOpaque ← mvarId.getKind then
        try mainGoalDischarger g; return (true, names, #[])
        catch _ => return (false, names, #[g])
  let .app (.app rel lhs) rhs ← withReducible g.getType'
    | throwError "gcongr failed, not a relation"
  let some relName := rel.getAppFn.constName?
    | throwError "gcongr failed, relation head {rel} is not a constant"
  let (some lhsHead, lhsArgs) := lhs.withApp fun e a => (e.constName?, a)
    | if template.isNone then return (false, names, #[g])
      throwError "gcongr failed, {lhs} is not a constant"
  let (some rhsHead, rhsArgs) := rhs.withApp fun e a => (e.constName?, a)
    | if template.isNone then return (false, names, #[g])
      throwError "gcongr failed, {rhs} is not a constant"
  let tplArgs ← if let some tpl := template then
    let (some tplHead, tplArgs) := tpl.withApp fun e a => (e.constName?, a)
      | throwError "gcongr failed, {tpl} is not a constant"
    unless tplHead == lhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {lhsHead}\n{lhs}"
    unless tplHead == rhsHead && tplArgs.size == rhsArgs.size do
      throwError "expected {tplHead}, got {rhsHead}\n{rhs}"
    tplArgs.mapM fun tpl => do
      let mctx ← getMCtx
      let hasMVar := tpl.findMVar? fun mvarId =>
        if let some mdecl := mctx.findDecl? mvarId then
          mdecl.kind matches .syntheticOpaque
        else
          false
      pure (some tpl, hasMVar.isSome)
  else
    unless lhsHead == rhsHead && lhsArgs.size == rhsArgs.size do
      return (false, names, #[g])
    (lhsArgs.zip rhsArgs).mapM fun (lhsArg, rhsArg) => do
      let isSame ← withReducibleAndInstances <|
        return (← isDefEq lhsArg rhsArg) || ((← isProof lhsArg) && (← isProof rhsArg))
      return (none, !isSame)
  let varyingArgs := tplArgs.map (·.2)
  if varyingArgs.all not then
    throwError "try rfl"
  let s ← saveState
  let mut ex? := none
  for lem in (gcongrExt.getState (← getEnv)).getD (relName, lhsHead, varyingArgs) #[] do
    let gs ← try
      Except.ok <$> withReducibleAndInstances (g.apply (← mkConstWithFreshMVarLevels lem.declName))
    catch e => pure (Except.error e)
    match gs with
    | .error e =>
      ex? := ex? <|> (some (← saveState, e))
      s.restore
    | .ok gs =>
      let some e ← getExprMVarAssignment? g | panic! "unassigned?"
      let args := e.getAppArgs
      let mut subgoals := #[]
      let mut names := names
      for (i, j) in lem.mainSubgoals do
        let some (.mvar mvarId) := args[i]? | panic! "what kind of lemma is this?"
        let (names2, _vs, mvarId) ← mvarId.introsWithBinderIdents names
        let tpl ← tplArgs[j]!.1.mapM fun e => do
          let (_vs, _, e) ← lambdaMetaTelescope e
          pure e
        let (_, names2, subgoals2) ← mvarId.gcongr tpl names2 mainGoalDischarger sideGoalDischarger
        (names, subgoals) := (names2, subgoals ++ subgoals2)
      let mut out := #[]
      for g in gs do
        if !(← g.isAssigned) && !subgoals.contains g then
          let s ← saveState
          try
            let (_, g') ← g.intros
            sideGoalDischarger g'
          catch _ =>
            s.restore
            out := out.push g
      return (true, names, out ++ subgoals)
  if template.isNone then
    return (false, names, #[g])
  let some (sErr, e) := ex?
    | throwError "gcongr failed, no @[gcongr] lemma applies for the template portion \
        {template} and the relation {rel}"
  sErr.restore
  throw e
elab "gcongr" template:(colGt term)?
    withArg:((" with " (colGt binderIdent)+)?) : tactic => do
  let g ← getMainGoal
  g.withContext do
  let .app (.app _rel lhs) _rhs ← withReducible g.getType'
    | throwError "gcongr failed, not a relation"
  let template ← template.mapM fun e => do
    Term.elabTerm e (← inferType lhs)
  let names := (withArg.raw[1].getArgs.map TSyntax.mk).toList
  let (progress, _, unsolvedGoalStates) ← g.gcongr template names
  if progress then
    replaceMainGoal unsolvedGoalStates.toList
  else
    throwError "gcongr did not make progress"
syntax "rel" " [" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| rel [$hyps,*]) => do
    let g ← getMainGoal
    g.withContext do
    let hyps ← hyps.getElems.mapM (elabTerm · none)
    let .app (.app _rel lhs) rhs ← withReducible g.getType'
      | throwError "rel failed, goal not a relation"
    unless ← isDefEq (← inferType lhs) (← inferType rhs) do
      throwError "rel failed, goal not a relation"
    let assum g := g.gcongrForward hyps
    let (_, _, unsolvedGoalStates) ← g.gcongr none [] (mainGoalDischarger := assum)
    match unsolvedGoalStates.toList with
    | [] => pure ()
    | unsolvedGoalStates => do
      let unsolvedGoals ← @List.mapM MetaM _ _ _ MVarId.getType unsolvedGoalStates
      let g := Lean.MessageData.joinSep (unsolvedGoals.map Lean.MessageData.ofExpr) Format.line
      throwError "rel failed, cannot prove goal by 'substituting' the listed relationships. \
        The steps which could not be automatically justified were:\n{g}"
end GCongr
end Mathlib.Tactic