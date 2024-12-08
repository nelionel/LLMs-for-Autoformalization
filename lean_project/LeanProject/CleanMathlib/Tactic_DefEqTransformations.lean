import Mathlib.Tactic.Basic
namespace Mathlib.Tactic
open Lean Meta Elab Elab.Tactic
def _root_.Lean.MVarId.changeLocalDecl' (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let lctx := (← mvarId.getDecl).lctx
  let some decl := lctx.find? fvarId | throwTacticEx `changeLocalDecl mvarId m!"\
    local variable {Expr.fvar fvarId} is not present in local context{mvarId}"
  let toRevert := lctx.foldl (init := #[]) fun arr decl' =>
    if decl.index ≤ decl'.index then arr.push decl'.fvarId else arr
  let (_, mvarId) ← mvarId.withReverted toRevert fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map .some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId
def runDefEqTactic (m : Option FVarId → Expr → MetaM Expr)
    (loc? : Option (TSyntax ``Parser.Tactic.location))
    (tacticName : String)
    (checkDefEq : Bool := true) :
    TacticM Unit := withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
    (atLocal := fun h => liftMetaTactic1 fun mvarId => do
      let ty ← h.getType
      let ty' ← m h (← instantiateMVars ty)
      if Expr.equal ty ty' then
        return mvarId
      else
        mvarId.changeLocalDecl' (checkDefEq := checkDefEq) h ty')
    (atTarget := liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← mvarId.getType)
      mvarId.change (checkDefEq := checkDefEq) (← m none ty))
    (failed := fun _ => throwError "{tacticName} failed")
def runDefEqConvTactic (m : Expr → MetaM Expr) : TacticM Unit := withMainContext do
  Conv.changeLhs <| ← m (← instantiateMVars <| ← Conv.getLhs)
elab "whnf" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ => whnf) loc? "whnf"
elab (name := betaReduceStx) "beta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ e => Core.betaReduce e) loc? "beta_reduce"
@[inherit_doc betaReduceStx]
elab "beta_reduce" : conv => runDefEqConvTactic (Core.betaReduce ·)
elab "reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ e => reduce e (skipTypes := false) (skipProofs := false)) loc? "reduce"
def unfoldFVars (fvars : Array FVarId) (e : Expr) : MetaM Expr := do
  transform (usedLetOnly := true) e fun node => do
    match node with
    | .fvar fvarId =>
      if fvars.contains fvarId then
        if let some val ← fvarId.getValue? then
          return .visit (← instantiateMVars val)
        else
          return .continue
      else
        return .continue
    | _ => return .continue
@[deprecated unfold (since := "2024-11-11")]
syntax (name := unfoldLetStx) "unfold_let" (ppSpace colGt term:max)*
  (ppSpace Parser.Tactic.location)? : tactic
elab_rules : tactic
  | `(tactic| unfold_let $[$loc?]?) => do
    logWarning "The `unfold_let` tactic is deprecated. Please use `unfold` instead."
    runDefEqTactic (fun _ => zetaReduce) loc? "unfold_let"
  | `(tactic| unfold_let $hs:term* $[$loc?]?) => do
    let fvars ← getFVarIds hs
    logWarning "The `unfold_let` tactic is deprecated. Please use `unfold` instead."
    runDefEqTactic (fun _ => unfoldFVars fvars) loc? "unfold_let"
@[inherit_doc unfoldLetStx, deprecated unfold (since := "2024-11-11")]
syntax "unfold_let" (ppSpace colGt term:max)* : conv
elab_rules : conv
  | `(conv| unfold_let) => do
    logWarning "The `unfold_let` tactic is deprecated. Please use `unfold` instead."
    runDefEqConvTactic zetaReduce
  | `(conv| unfold_let $hs:term*) => do
    logWarning "The `unfold_let` tactic is deprecated. Please use `unfold` instead."
    runDefEqConvTactic (unfoldFVars (← getFVarIds hs))
def refoldFVars (fvars : Array FVarId) (loc? : Option FVarId) (e : Expr) : MetaM Expr := do
  let fvars ←
    if let some loc := loc? then
      let locIndex := (← loc.getDecl).index
      fvars.filterM fun fvar => do
        let some decl ← fvar.findDecl? | return false
        return decl.index < locIndex
    else
      pure fvars
  let mut e := e
  for fvar in fvars do
    let some val ← fvar.getValue?
      | throwError "local variable {Expr.fvar fvar} has no value to refold"
    e := (← kabstract e val).instantiate1 (Expr.fvar fvar)
  return e
syntax (name := refoldLetStx) "refold_let" (ppSpace colGt term:max)*
  (ppSpace Parser.Tactic.location)? : tactic
elab_rules : tactic
  | `(tactic| refold_let $hs:term* $[$loc?]?) => do
    let fvars ← getFVarIds hs
    runDefEqTactic (refoldFVars fvars) loc? "refold_let"
@[inherit_doc refoldLetStx]
syntax "refold_let" (ppSpace colGt term:max)* : conv
elab_rules : conv
  | `(conv| refold_let $hs:term*) => do
    runDefEqConvTactic (refoldFVars (← getFVarIds hs) none)
def unfoldProjs (e : Expr) : MetaM Expr := do
  transform e fun node => do
    if let some node' ← unfoldProjInst? node then
      return .visit (← instantiateMVars node')
    else
      return .continue
elab (name := unfoldProjsStx) "unfold_projs" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => unfoldProjs) loc? "unfold_projs"
@[inherit_doc unfoldProjsStx]
elab "unfold_projs" : conv => runDefEqConvTactic unfoldProjs
def etaReduceAll (e : Expr) : MetaM Expr := do
  transform e fun node =>
    match node.etaExpandedStrict? with
    | some e' => return .visit e'
    | none => return .continue
elab (name := etaReduceStx) "eta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaReduceAll) loc? "eta_reduce"
@[inherit_doc etaReduceStx]
elab "eta_reduce" : conv => runDefEqConvTactic etaReduceAll
partial def etaExpandAll (e : Expr) : MetaM Expr := do
  let betaOrApp (f : Expr) (args : Array Expr) : Expr :=
    if f.etaExpanded?.isSome then f.beta args else mkAppN f args
  let expand (e : Expr) : MetaM Expr := do
    if e.isLambda then
      return e
    else
      forallTelescopeReducing (← inferType e) fun xs _ => do
        mkLambdaFVars xs (betaOrApp e xs)
  transform e
    (pre := fun node => do
      if node.isApp then
        let f ← etaExpandAll node.getAppFn
        let args ← node.getAppArgs.mapM etaExpandAll
        .done <$> expand (betaOrApp f args)
      else
        pure .continue)
    (post := (.done <$> expand ·))
elab (name := etaExpandStx) "eta_expand" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaExpandAll) loc? "eta_expand"
@[inherit_doc etaExpandStx]
elab "eta_expand" : conv => runDefEqConvTactic etaExpandAll
def getProjectedExpr (e : Expr) : MetaM (Option (Name × Nat × Expr)) := do
  if let .proj S i x := e then
    return (S, i, x)
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if e.getAppNumArgs == info.numParams + 1 then
        if let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? info.ctorName then
          return (fVal.induct, info.i, e.appArg!)
  return none
def etaStruct? (e : Expr) (tryWhnfR : Bool := true) : MetaM (Option Expr) := do
  let .const f _ := e.getAppFn | return none
  let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? f | return none
  unless 0 < fVal.numFields && e.getAppNumArgs == fVal.numParams + fVal.numFields do return none
  unless isStructureLike (← getEnv) fVal.induct do return none
  let args := e.getAppArgs
  let mut x? ← findProj fVal args pure
  if tryWhnfR then
    if let .undef := x? then
      x? ← findProj fVal args whnfR
  if let .some x := x? then
    if ← isDefEq x e then
      return x
  return none
where
  findProj (fVal : ConstructorVal) (args : Array Expr) (m : Expr → MetaM Expr) :
      MetaM (LOption Expr) := do
    for i in [0 : fVal.numFields] do
      let arg ← m args[fVal.numParams + i]!
      let some (S, j, x) ← getProjectedExpr arg | continue
      if S == fVal.induct && i == j then
        return .some x
      else
        return .none
    return .undef
def etaStructAll (e : Expr) : MetaM Expr :=
  transform e fun node => do
    if let some node' ← etaStruct? node then
      return .visit node'
    else
      return .continue
elab (name := etaStructStx) "eta_struct" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaStructAll) loc? "eta_struct"
@[inherit_doc etaStructStx]
elab "eta_struct" : conv => runDefEqConvTactic etaStructAll
end Mathlib.Tactic