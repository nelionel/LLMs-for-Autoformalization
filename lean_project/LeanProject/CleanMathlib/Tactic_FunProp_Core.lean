import Mathlib.Tactic.FunProp.Theorems
import Mathlib.Tactic.FunProp.ToBatteries
import Mathlib.Tactic.FunProp.Types
import Mathlib.Lean.Expr.Basic
import Batteries.Tactic.Exact
namespace Mathlib
open Lean Meta Qq
namespace Meta.FunProp
def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
  match (← trySynthInstance type) with
  | LOption.some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fun_prop]
"{← ppOrigin thmId}, failed to assign instance{indentExpr type}
synthesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
      return false
  | _ =>
    trace[Meta.Tactic.fun_prop]
      "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
    return false
def synthesizeArgs (thmId : Origin) (xs : Array Expr)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM Bool := do
  let mut postponed : Array Expr := #[]
  for x in xs do
    let type ← inferType x
    if (← instantiateMVars x).isMVar then
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue
      else if (← isFunProp type.getForallBody) then
        if let .some ⟨proof⟩ ← funProp type then
          if (← isDefEq x proof) then
            continue
          else do
            trace[Meta.Tactic.fun_prop]
              "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return false
      else
        let ctx : Context ← read
        if (← isProp type) then
          if let .some proof ← ctx.disch type then
            if (← isDefEq x proof) then
              continue
            else do
              trace[Meta.Tactic.fun_prop]
                "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
              return false
          else
            logError s!"Failed to prove necessary assumption `{← ppExpr type}` \
                        when applying theorem `{← ppOrigin' thmId}`."
      if ¬(← isProp type) then
        postponed := postponed.push x
        continue
      else
        trace[Meta.Tactic.fun_prop]
          "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
        return false
  for x in postponed do
    if (← instantiateMVars x).isMVar then
      logError s!"Failed to infer `({← ppExpr x} : {← ppExpr (← inferType x)})` \
      when applying theorem `{← ppOrigin' thmId}`."
      trace[Meta.Tactic.fun_prop]
        "{← ppOrigin thmId}, failed to infer `({← ppExpr x} : {← ppExpr (← inferType x)})`"
      return false
  return true
def tryTheoremCore (xs : Array Expr) (val : Expr) (type : Expr) (e : Expr)
    (thmId : Origin) (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  withTraceNode `Meta.Tactic.fun_prop
    (fun r => return s!"[{ExceptToEmoji.toEmoji r}] applying: {← ppOrigin' thmId}") do
  if (← isDefEq type e) then
    if ¬(← synthesizeArgs thmId xs funProp) then
      return none
    let proof ← instantiateMVars (mkAppN val xs)
    return .some { proof := proof }
  else
    trace[Meta.Tactic.fun_prop] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"
    return none
def tryTheoremWithHint? (e : Expr) (thmOrigin : Origin)
    (hint : Array (Nat×Expr))
    (funProp : Expr → FunPropM (Option Result)) (newMCtxDepth : Bool := false) :
    FunPropM (Option Result) := do
  let go : FunPropM (Option Result) := do
    let thmProof ← thmOrigin.getValue
    let type ← inferType thmProof
    let (xs, _, type) ← forallMetaTelescope type
    for (i,x) in hint do
      try
        for (id,v) in hint do
          xs[id]!.mvarId!.assignIfDefeq v
      catch _ =>
        trace[Debug.Meta.Tactic.fun_prop]
          "failed to use hint {i} `{← ppExpr x} when applying theorem {← ppOrigin thmOrigin}"
    tryTheoremCore xs thmProof type e thmOrigin funProp
  if newMCtxDepth then
    withNewMCtxDepth go
  else
    go
def tryTheorem? (e : Expr) (thmOrigin : Origin) (funProp : Expr → FunPropM (Option Result))
    (newMCtxDepth : Bool := false) : FunPropM (Option Result) :=
  tryTheoremWithHint? e thmOrigin #[] funProp newMCtxDepth
def applyIdRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms ← getLambdaTheorems funPropDecl.funPropName .id
  if thms.size = 0 then
    let msg := s!"missing identity rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    if let .some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r
  return none
def applyConstRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms ← getLambdaTheorems funPropDecl.funPropName .const
  if thms.size = 0 then
    let msg := s!"missing constant rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    let .const := thm.thmArgs | return none
    if let .some r ← tryTheorem? e (.decl thm.thmName) funProp then
      return r
  return none
def applyApplyRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms := (← getLambdaTheorems funPropDecl.funPropName .apply)
  for thm in thms do
    if let .some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r
  return none
def applyCompRule (funPropDecl : FunPropDecl) (e f g : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms ← getLambdaTheorems funPropDecl.funPropName .comp
  if thms.size = 0 then
    let msg := s!"missing composition rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    let .comp id_f id_g := thm.thmArgs | return none
    if let .some r ← tryTheoremWithHint? e (.decl thm.thmName) #[(id_f,f),(id_g,g)] funProp then
      return r
  return none
def applyPiRule (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let thms ← getLambdaTheorems funPropDecl.funPropName .pi
  if thms.size = 0 then
    let msg := s!"missing pi rule to prove `{← ppExpr e}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    if let .some r ← tryTheoremWithHint? e (.decl thm.thmName) #[] funProp then
      return r
  return none
def letCase (funPropDecl : FunPropDecl) (e : Expr) (f : Expr)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do
  match f with
  | .lam xName xType (.letE yName yType yValue yBody _) xBi => do
    let yType  := yType.consumeMData
    let yValue := yValue.consumeMData
    let yBody  := yBody.consumeMData
    let yType := yType.headBeta
    if (yType.hasLooseBVar 0) then
      throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)}"
    if ¬(yValue.hasLooseBVar 0) then
      let body := yBody.swapBVars 0 1
      let e' := .letE yName yType yValue (nonDep := false)
        (e.setArg (funPropDecl.funArgId) (.lam xName xType body xBi))
      return ← funProp e'
    match (yBody.hasLooseBVar 0), (yBody.hasLooseBVar 1) with
    | true, true =>
      let f ← mkUncurryFun 2 (Expr.lam xName xType (.lam yName yType yBody default) xBi)
      let g := Expr.lam xName xType (binderInfo := default)
        (mkAppN (← mkConstWithFreshMVarLevels ``Prod.mk) #[xType,yType,.bvar 0, yValue])
      applyCompRule funPropDecl e f g funProp
    | true, false =>
      let f := Expr.lam yName yType yBody default
      let g := Expr.lam xName xType yValue default
      applyCompRule funPropDecl e f g funProp
    | false, _ =>
      let f := Expr.lam xName xType (yBody.lowerLooseBVars 1 1) xBi
      funProp (e.setArg (funPropDecl.funArgId) f)
  | _ => throwError "expected expression of the form `fun x => lam y := ..; ..`"
def applyMorRules (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  trace[Debug.Meta.Tactic.fun_prop] "applying morphism theorems to {← ppExpr e}"
  match ← fData.isMorApplication with
  | .none => throwError "fun_prop bug: invalid use of mor rules on {← ppExpr e}"
  | .underApplied =>
    applyPiRule funPropDecl e funProp
  | .overApplied =>
    let .some (f,g) ← fData.peeloffArgDecomposition | return none
    applyCompRule funPropDecl e f g funProp
  | .exact =>
    let candidates ← getMorphismTheorems e
    trace[Meta.Tactic.fun_prop]
      "candidate morphism theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"
    for c in candidates do
      if let .some r ← tryTheorem? e (.decl c.thmName) funProp then
        return r
    trace[Debug.Meta.Tactic.fun_prop] "no theorem matched"
    return none
def applyTransitionRules (e : Expr) (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do
  withIncreasedTransitionDepth do
  let candidates ← getTransitionTheorems e
  trace[Meta.Tactic.fun_prop]
    "candidate transition theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"
  for c in candidates do
    if let .some r ← tryTheorem? e (.decl c.thmName) funProp then
      return r
  trace[Debug.Meta.Tactic.fun_prop] "no theorem matched"
  return none
def removeArgRule (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do
  match fData.args.size with
  | 0 => throwError "fun_prop bug: invalid use of remove arg case {←ppExpr e}"
  | _ =>
    let n := fData.args.size
    let arg := fData.args[n-1]!
    if arg.coe.isSome then
      return ← applyMorRules funPropDecl e fData funProp
    else
      let .some (f,g) ← fData.peeloffArgDecomposition | return none
      applyCompRule funPropDecl e f g funProp
def bvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  if (← fData.isMorApplication) != .none then
    applyMorRules funPropDecl e fData funProp
  else
    if let .some (f, g) ← fData.nontrivialDecomposition then
      applyCompRule funPropDecl e f g funProp
    else
      applyApplyRule funPropDecl e funProp
def getDeclTheorems (funPropDecl : FunPropDecl) (funName : Name)
    (mainArgs : Array Nat) (appliedArgs : Nat) : MetaM (Array FunctionTheorem) := do
  let thms ← getTheoremsForFunction funName funPropDecl.funPropName
  let thms := thms
    |>.filter (fun thm => (isOrderedSubsetOf mainArgs thm.mainArgs))
    |>.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat appliedArgs).natAbs
      match compare dt ds with
      | .lt => true
      | .gt => false
      | .eq => t.mainArgs.size < s.mainArgs.size)
  return thms
def getLocalTheorems (funPropDecl : FunPropDecl) (funOrigin : Origin)
    (mainArgs : Array Nat) (appliedArgs : Nat) : FunPropM (Array FunctionTheorem) := do
  let mut thms : Array FunctionTheorem := #[]
  let lctx ← getLCtx
  for var in lctx do
    if (var.kind = Lean.LocalDeclKind.auxDecl) then
      continue
    let type ← instantiateMVars var.type
    let thm? : Option FunctionTheorem ←
      forallTelescope type fun _ b => do
      let b ← whnfR b
      let .some (decl,f) ← getFunProp? b | return none
      unless decl.funPropName = funPropDecl.funPropName do return none
      let .data fData ← getFunctionData? f (← unfoldNamePred)
        | return none
      unless (fData.getFnOrigin == funOrigin) do return none
      unless isOrderedSubsetOf mainArgs fData.mainArgs do return none
      let dec? ← fData.nontrivialDecomposition
      let thm : FunctionTheorem := {
        funPropName := funPropDecl.funPropName
        thmOrigin := .fvar var.fvarId
        funOrigin := funOrigin
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := eval_prio default
        form := if dec?.isSome then .comp else .uncurried
      }
      return .some thm
    if let .some thm := thm? then
      thms := thms.push thm
  thms := thms
    |>.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat appliedArgs).natAbs
      match compare dt ds with
      | .lt => true
      | .gt => false
      | .eq => t.mainArgs.size < s.mainArgs.size)
  return thms
def tryTheorems (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (thms : Array FunctionTheorem) (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do
  let mut dec? : Option (Option (Expr × Expr)) := none
  for thm in thms do
    trace[Debug.Meta.Tactic.fun_prop] s!"trying theorem {← ppOrigin' thm.thmOrigin}"
    match compare thm.appliedArgs fData.args.size with
    | .lt =>
      trace[Meta.Tactic.fun_prop] s!"removing argument to later use {← ppOrigin' thm.thmOrigin}"
      if let .some r ← removeArgRule funPropDecl e fData funProp then
        return r
      continue
    | .gt =>
      trace[Meta.Tactic.fun_prop] s!"adding argument to later use {← ppOrigin' thm.thmOrigin}"
      if let .some r ← applyPiRule funPropDecl e funProp then
        return r
      continue
    | .eq =>
      if thm.form == .comp then
        if let .some r ← tryTheorem? e thm.thmOrigin funProp then
          return r
      else
        if thm.mainArgs.size == fData.mainArgs.size then
          if dec?.isNone then
            dec? := .some (← fData.nontrivialDecomposition)
          match dec? with
          | .some .none =>
            if let .some r ← tryTheorem? e thm.thmOrigin funProp then
              return r
          | .some (.some (f,g)) =>
            trace[Meta.Tactic.fun_prop]
              s!"decomposing to later use {←ppOrigin' thm.thmOrigin} as:
                   ({← ppExpr f}) ∘ ({← ppExpr g})"
            if let .some r ← applyCompRule funPropDecl e f g funProp then
              return r
          | _ => continue
        else
          let .some (f,g) ← fData.decompositionOverArgs thm.mainArgs
            | continue
          trace[Meta.Tactic.fun_prop]
            s!"decomposing to later use {←ppOrigin' thm.thmOrigin} as:
                 ({← ppExpr f}) ∘ ({← ppExpr g})"
          if let .some r ← applyCompRule funPropDecl e f g funProp then
            return r
  return none
def fvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  if let .some (f,g) ← fData.nontrivialDecomposition then
    applyCompRule funPropDecl e f g funProp
  else
    let .fvar id := fData.fn | throwError "fun_prop bug: invalid use of fvar app case"
    let thms ← getLocalTheorems funPropDecl (.fvar id) fData.mainArgs fData.args.size
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {←ppExpr (.fvar id)} \
         {← thms.mapM fun thm => ppOrigin' thm.thmOrigin}"
    if let .some r ← tryTheorems funPropDecl e fData thms funProp then
      return r
    if let .some f ← fData.unfoldHeadFVar? then
      let e' := e.setArg funPropDecl.funArgId f
      if let .some r ← funProp e' then
        return r
    if (← fData.isMorApplication) != .none then
      if let .some r ← applyMorRules funPropDecl e fData funProp then
        return r
    if (← fData.nontrivialDecomposition).isNone then
      if let .some r ← applyTransitionRules e funProp then
        return r
    if thms.size = 0 then
      logError s!"No theorems found for `{← ppExpr (.fvar id)}` in order to prove `{← ppExpr e}`"
    return none
def constAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let .some (funName,_) := fData.fn.const?
    | throwError "fun_prop bug: invelid use of const app case"
  let globalThms ← getDeclTheorems funPropDecl funName fData.mainArgs fData.args.size
  trace[Meta.Tactic.fun_prop]
    s!"candidate theorems for {funName} {← globalThms.mapM fun thm => ppOrigin' thm.thmOrigin}"
  if let .some r ← tryTheorems funPropDecl e fData globalThms funProp then
    return r
  let localThms ← getLocalTheorems funPropDecl (.decl funName) fData.mainArgs fData.args.size
  if localThms.size ≠ 0 then
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {funName} \
        {← localThms.mapM fun thm => ppOrigin' thm.thmOrigin}"
  if let .some r ← tryTheorems funPropDecl e fData localThms funProp then
    return r
  if globalThms.size = 0 && localThms.size = 0 then
     logError s!"No theorems found for `{funName}` in order to prove `{← ppExpr e}`"
  if (← fData.isMorApplication) != .none then
    if let .some r ← applyMorRules funPropDecl e fData funProp then
      return r
  if let .some (f,g) ← fData.nontrivialDecomposition then
    trace[Meta.Tactic.fun_prop]
      s!"failed applying `{funPropDecl.funPropName}` theorems for `{funName}`
         trying again after decomposing function as: `({← ppExpr f}) ∘ ({← ppExpr g})`"
    if let .some r ← applyCompRule funPropDecl e f g funProp then
      return r
  else
    trace[Meta.Tactic.fun_prop]
      s!"failed applying `{funPropDecl.funPropName}` theorems for `{funName}`
         now trying to prove `{funPropDecl.funPropName}` from another function property"
    if let .some r ← applyTransitionRules e funProp then
      return r
  return none
def cacheResult (e : Expr) (r : Result) : FunPropM Result := do 
  modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof} })
  return r
def cacheFailure (e : Expr) : FunPropM Unit := do 
  modify (fun s => { s with failureCache := s.failureCache.insert e })
mutual
  partial def funProp (e : Expr) : FunPropM (Option Result) := do
    let e ← instantiateMVars e
    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] {← ppExpr e}") do
    if let .some { expr := _, proof? := .some proof } := (← get).cache.find? e then
      trace[Meta.Tactic.fun_prop] "reusing previously found proof for {e}"
      return .some { proof := proof }
    else if (← get).failureCache.contains e then
      trace[Meta.Tactic.fun_prop] "skipping proof search, proving {e} was tried already and failed"
      return .none
    else
      match e with
      | .letE .. =>
        letTelescope e fun xs b => do
          let .some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars xs r.proof }
      | .forallE .. =>
        forallTelescope e fun xs b => do
          let .some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars xs r.proof }
      | .mdata _ e' => funProp e'
      | _ =>
        if let .some r ← main e then
          cacheResult e r
        else
          cacheFailure e
          return none
  private partial def main (e : Expr) : FunPropM (Option Result) := do
    let .some (funPropDecl, f) ← getFunProp? e
      | return none
    increaseSteps
    if f.isLet then
      return ← letTelescope f fun xs b => do
        let e' := e.setArg funPropDecl.funArgId b
        funProp (← mkLambdaFVars xs e')
    match ← getFunctionData? f (← unfoldNamePred) with
    | .letE f =>
      trace[Debug.Meta.Tactic.fun_prop] "let case on {← ppExpr f}"
      let e := e.setArg funPropDecl.funArgId f 
      letCase funPropDecl e f funProp
    | .lam f =>
      trace[Debug.Meta.Tactic.fun_prop] "pi case on {← ppExpr f}"
      let e := e.setArg funPropDecl.funArgId f 
      applyPiRule funPropDecl e funProp
    | .data fData =>
      let e := e.setArg funPropDecl.funArgId (← fData.toExpr) 
      if fData.isIdentityFun then
        applyIdRule funPropDecl e funProp
      else if fData.isConstantFun then
        applyConstRule funPropDecl e funProp
      else
        match fData.fn with
        | .fvar id =>
          if id == fData.mainVar.fvarId! then
            bvarAppCase funPropDecl e fData funProp
          else
            fvarAppCase funPropDecl e fData funProp
        | .const .. | .proj .. => do
          constAppCase funPropDecl e fData funProp
        | _ =>
          trace[Debug.Meta.Tactic.fun_prop] "unknown case, ctor: {f.ctorName}\n{e}"
          return none
end
end Meta.FunProp
end Mathlib