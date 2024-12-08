import Qq
import Mathlib.Tactic.FunProp.Mor
namespace Mathlib
open Lean Meta
namespace Meta.FunProp
structure FunctionData where
  lctx : LocalContext
  insts : LocalInstances
  fn : Expr
  args : Array Mor.Arg
  mainVar : Expr
  mainArgs : Array Nat
def FunctionData.toExpr (f : FunctionData) : MetaM Expr := do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body
def FunctionData.isIdentityFun (f : FunctionData) : Bool :=
  (f.args.size = 0 && f.fn == f.mainVar)
def FunctionData.isConstantFun (f : FunctionData) : Bool :=
  ((f.mainArgs.size = 0) && !(f.fn.containsFVar f.mainVar.fvarId!))
def FunctionData.domainType (f : FunctionData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    inferType f.mainVar
def FunctionData.getFnConstName? (f : FunctionData) : MetaM (Option Name) := do
  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ =>
    let .some info := getStructureInfo? (← getEnv) typeName | return none
    let .some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none
def getFunctionData (f : Expr) : MetaM FunctionData := do
  lambdaTelescope f fun xs b => do
    let xId := xs[0]!.fvarId!
    Mor.withApp b fun fn args => do
      let mut fn := fn
      let mut args := args
      if let .proj n i x := fn then
        let .some info := getStructureInfo? (← getEnv) n | unreachable!
        let .some projName := info.getProjFn? i | unreachable!
        let p ← mkAppM projName #[x]
        fn := p.getAppFn
        args := p.getAppArgs.map (fun a => {expr:=a}) ++ args
      let mainArgs := args
        |>.mapIdx (fun i ⟨arg,_⟩ => if arg.containsFVar xId then some i else none)
        |>.filterMap id
      return {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        fn := fn
        args := args
        mainVar := xs[0]!
        mainArgs := mainArgs
      }
inductive MaybeFunctionData where
  | letE (f : Expr)
  | lam (f : Expr)
  | data (fData : FunctionData)
def MaybeFunctionData.get (fData : MaybeFunctionData) : MetaM Expr :=
  match fData with
  | .letE f | .lam f => pure f
  | .data d => d.toExpr
def getFunctionData? (f : Expr)
    (unfoldPred : Name → Bool := fun _ => false) :
    MetaM MaybeFunctionData := do
  withConfig (fun cfg => { cfg with zeta := false, zetaDelta := false }) do
  let unfold := fun e : Expr => do
    if let .some n := e.getAppFn'.constName? then
      pure ((unfoldPred n) || (← isReducible n))
    else
      pure false
  let .forallE xName xType _ _ ← instantiateMVars (← inferType f)
    | throwError m!"fun_prop bug: function expected, got `{f} : {← inferType f}, \
                    type ctor {(← inferType f).ctorName}"
  withLocalDeclD xName xType fun x => do
    let fx' := (← Mor.whnfPred (f.beta #[x]).eta unfold) |> headBetaThroughLet
    let f' ← mkLambdaFVars #[x] fx'
    match fx' with
    | .letE .. => return .letE f'
    | .lam  .. => return .lam f'
    | _ => return .data (← getFunctionData f')
def FunctionData.unfoldHeadFVar? (fData : FunctionData) : MetaM (Option Expr) := do
  let .fvar id := fData.fn | return none
  let .some val ← id.getValue? | return none
  let f ← withLCtx fData.lctx fData.insts do
    mkLambdaFVars #[fData.mainVar] (headBetaThroughLet (Mor.mkAppN val fData.args))
  return f
inductive MorApplication where
  | underApplied
  | exact
  | overApplied
  | none
  deriving Inhabited, BEq
def FunctionData.isMorApplication (f : FunctionData) : MetaM MorApplication := do
  if let .some name := f.fn.constName? then
    if ← Mor.isCoeFunName name then
      let info ← getConstInfo name
      let arity := info.type.getNumHeadForalls
      match compare arity f.args.size with
      | .eq => return .exact
      | .lt => return .overApplied
      | .gt => return .underApplied
  match f.args.size with
  | 0 => return .none
  | _ =>
    let n := f.args.size
    if f.args[n-1]!.coe.isSome then
      return .exact
    else if f.args.any (fun a => a.coe.isSome) then
      return .overApplied
    else
      return .none
def FunctionData.peeloffArgDecomposition (fData : FunctionData) : MetaM (Option (Expr × Expr)) := do
  unless fData.args.size > 0 do return none
  withLCtx fData.lctx fData.insts do
    let n := fData.args.size
    let x := fData.mainVar
    let yₙ := fData.args[n-1]!
    if yₙ.expr.containsFVar x.fvarId! then
      return none
    if fData.args.size = 1 &&
       fData.mainVar == fData.fn then
      return none
    let gBody' := Mor.mkAppN fData.fn fData.args[:n-1]
    let gBody' := if let .some coe := yₙ.coe then coe.app gBody' else gBody'
    let g' ← mkLambdaFVars #[x] gBody'
    let f' := Expr.lam `f (← inferType gBody') (.app (.bvar 0) (yₙ.expr)) default
    return (f',g')
def FunctionData.nontrivialDecomposition (fData : FunctionData) : MetaM (Option (Expr × Expr)) := do
    let mut lctx := fData.lctx
    let insts := fData.insts
    let x := fData.mainVar
    let xId := x.fvarId!
    let xName ← withLCtx lctx insts xId.getUserName
    let fn := fData.fn
    let mut args := fData.args
    if fn.containsFVar xId then
      return ← fData.peeloffArgDecomposition
    let mut yVals : Array Expr := #[]
    let mut yVars : Array Expr := #[]
    for argId in fData.mainArgs do
      let yVal := args[argId]!
      let yVal' := yVal.expr
      let yId ← withLCtx lctx insts mkFreshFVarId
      let yType ← withLCtx lctx insts (inferType yVal')
      if yType.containsFVar fData.mainVar.fvarId! then
        return none
      lctx := lctx.mkLocalDecl yId (xName.appendAfter (toString argId)) yType
      let yVar := Expr.fvar yId
      yVars := yVars.push yVar
      yVals := yVals.push yVal'
      args := args.set! argId ⟨yVar, yVal.coe⟩
    let g  ← withLCtx lctx insts do
      mkLambdaFVars #[x] (← mkProdElem yVals)
    let f ← withLCtx lctx insts do
      (mkLambdaFVars yVars (Mor.mkAppN fn args))
      >>=
      mkUncurryFun yVars.size
    let f' ← fData.toExpr
    if (← isDefEq f' f) || (← isDefEq f' g) then
      return none
    return (f, g)
def FunctionData.decompositionOverArgs (fData : FunctionData) (args : Array Nat) :
    MetaM (Option (Expr × Expr)) := do
  unless isOrderedSubsetOf fData.mainArgs args do return none
  unless ¬(fData.fn.containsFVar fData.mainVar.fvarId!) do return none
  withLCtx fData.lctx fData.insts do
  let gxs := args.map (fun i => fData.args[i]!.expr)
  try
    let gx ← mkProdElem gxs 
    let g ← withLCtx fData.lctx fData.insts <| mkLambdaFVars #[fData.mainVar] gx
    withLocalDeclD `y (← inferType gx) fun y => do
      let ys ← mkProdSplitElem y gxs.size
      let args' := (args.zip ys).foldl (init := fData.args)
          (fun args' (i,y) => args'.set! i { expr := y, coe := args'[i]!.coe })
      let f ← mkLambdaFVars #[y] (Mor.mkAppN fData.fn args')
      return (f,g)
  catch _ =>
    return none
end Meta.FunProp
end Mathlib