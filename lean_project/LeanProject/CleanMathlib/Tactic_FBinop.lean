import Lean.Elab.App
import Lean.Elab.BuiltinNotation
import Mathlib.Tactic.ToExpr
namespace FBinopElab
open Lean Elab Term Meta
initialize registerTraceClass `Elab.fbinop
syntax:max (name := prodSyntax) "fbinop% " ident ppSpace term:max ppSpace term:max : term
private inductive Tree where
  | term (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
  | binop (ref : Syntax) (f : Expr) (lhs rhs : Tree)
  | macroExpansion (macroName : Name) (stx stx' : Syntax) (nested : Tree)
private partial def toTree (s : Syntax) : TermElabM Tree := do
  let result ← go s
  synthesizeSyntheticMVars (postpone := .yes)
  return result
where
  go (s : Syntax) : TermElabM Tree := do
    match s with
    | `(fbinop% $f $lhs $rhs) => processBinOp s f lhs rhs
    | `(($e)) =>
      if hasCDot e then
        processLeaf s
      else
        go e
    | _ =>
      withRef s do
        match ← liftMacroM <| expandMacroImpl? (← getEnv) s with
        | some (macroName, s?) =>
          let s' ← liftMacroM <| liftExcept s?
          withPushMacroExpansionStack s s' do
            return .macroExpansion macroName s s' (← go s')
        | none => processLeaf s
  processBinOp (ref : Syntax) (f lhs rhs : Syntax) := do
    let some f ← resolveId? f | throwUnknownConstant f.getId
    return .binop ref f (← go lhs) (← go rhs)
  processLeaf (s : Syntax) := do
    let e ← elabTerm s none
    let info ← getResetInfoTrees
    return .term s info e
structure SRec where
  name : Name
  args : Array Expr
  deriving Inhabited, ToExpr
private partial def extractS (e : Expr) : TermElabM (Option (SRec × Expr)) :=
  match e with
  | .letE .. => extractS (e.letBody!.instantiate1 e.letValue!)
  | .mdata _ b => extractS b
  | .app .. => do
    let f := e.getAppFn
    let .const n _ := f | return none
    let mut args := e.getAppArgs
    let mut info := (← getFunInfoNArgs f args.size).paramInfo
    for _ in [0 : args.size - 1] do
      if info.back!.isInstImplicit then
        args := args.pop
        info := info.pop
      else
        break
    let x := args.back!
    unless ← Meta.isType x do return none
    return some ({name := n, args := args.pop}, x)
  | _ => return none
private def applyS (S : SRec) (x : Expr) : TermElabM (Option Expr) :=
  try
    let f ← mkConstWithFreshMVarLevels S.name
    let v ← elabAppArgs f #[] ((S.args.push x).map .expr)
      (expectedType? := none) (explicit := true) (ellipsis := false)
    elabAppArgs v #[] #[] (expectedType? := none) (explicit := false) (ellipsis := false)
  catch _ =>
    return none
private def hasCoeS (fromS toS : SRec) (x : Expr) : TermElabM Bool := do
  let some fromType ← applyS fromS x | return false
  let some toType ← applyS toS x | return false
  trace[Elab.fbinop] m!"fromType = {fromType}, toType = {toType}"
  withLocalDeclD `v fromType fun v => do
    match ← coerceSimple? v toType with
    | .some _ => return true
    | .none   => return false
    | .undef  => return false 
private structure AnalyzeResult where
  maxS? : Option SRec := none
  hasUncomparable : Bool := false
private def analyze (t : Tree) (expectedType? : Option Expr) : TermElabM AnalyzeResult := do
  let maxS? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if let some (S, _) ← extractS expectedType then
        pure S
      else
        pure none
  (go t *> get).run' { maxS? }
where
  go (t : Tree) : StateRefT AnalyzeResult TermElabM Unit := do
    unless (← get).hasUncomparable do
      match t with
      | .macroExpansion _ _ _ nested => go nested
      | .binop _ _ lhs rhs => go lhs; go rhs
      | .term _ _ val =>
        let type ← instantiateMVars (← inferType val)
        let some (S, x) ← extractS type
          | return 
        match (← get).maxS? with
        | none     => modify fun s => { s with maxS? := S }
        | some maxS =>
          let some maxSx ← applyS maxS x | return 
          unless ← withNewMCtxDepth <| isDefEqGuarded maxSx type do
            if ← hasCoeS S maxS x then
              return ()
            else if ← hasCoeS maxS S x then
              modify fun s => { s with maxS? := S }
            else
              trace[Elab.fbinop] "uncomparable types: {maxSx}, {type}"
              modify fun s => { s with hasUncomparable := true }
private def mkBinOp (f : Expr) (lhs rhs : Expr) : TermElabM Expr := do
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none)
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
private def toExprCore (t : Tree) : TermElabM Expr := do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref f lhs rhs =>
    withRef ref <| withTermInfoContext' .anonymous ref do
      let lhs ← toExprCore lhs
      let mut rhs ← toExprCore rhs
      mkBinOp f lhs rhs
  | .macroExpansion macroName stx stx' nested =>
    withRef stx <| withTermInfoContext' macroName stx do
      withMacroExpansion stx stx' do
        toExprCore nested
private def applyCoe (t : Tree) (maxS : SRec) : TermElabM Tree := do
  go t none
where
  go (t : Tree) (f? : Option Expr) : TermElabM Tree := do
    match t with
    | .binop ref f lhs rhs =>
      let lhs' ← go lhs f
      let rhs' ← go rhs f
      return .binop ref f lhs' rhs'
    | .term ref trees e =>
      let type ← instantiateMVars (← inferType e)
      trace[Elab.fbinop] "visiting {e} : {type}"
      let some (_, x) ← extractS type
        | 
          let x' ← mkFreshExprMVar none
          let some maxType ← applyS maxS x' | trace[Elab.fbinop] "mvar apply failed"; return t
          trace[Elab.fbinop] "defeq hint {maxType} =?= {type}"
          _ ← isDefEqGuarded maxType type
          return t
      let some maxType ← applyS maxS x
        | trace[Elab.fbinop] "applying {Lean.toExpr maxS} {x} failed"
          return t
      trace[Elab.fbinop] "{type} =?= {maxType}"
      if ← isDefEqGuarded maxType type then
        return t
      else
        trace[Elab.fbinop] "added coercion: {e} : {type} => {maxType}"
        withRef ref <| return .term ref trees (← mkCoe maxType e)
    | .macroExpansion macroName stx stx' nested =>
      withRef stx <| withPushMacroExpansionStack stx stx' do
        return .macroExpansion macroName stx stx' (← go nested f?)
private def toExpr (tree : Tree) (expectedType? : Option Expr) : TermElabM Expr := do
  let r ← analyze tree expectedType?
  trace[Elab.fbinop] "hasUncomparable: {r.hasUncomparable}, maxType: {Lean.toExpr r.maxS?}"
  if r.hasUncomparable || r.maxS?.isNone then
    let result ← toExprCore tree
    ensureHasType expectedType? result
  else
    let result ← toExprCore (← applyCoe tree r.maxS?.get!)
    trace[Elab.fbinop] "result: {result}"
    ensureHasType expectedType? result
@[term_elab prodSyntax]
def elabBinOp : TermElab := fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?
end FBinopElab