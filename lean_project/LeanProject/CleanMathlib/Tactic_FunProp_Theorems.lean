import Mathlib.Tactic.FunProp.Decl
import Mathlib.Tactic.FunProp.Types
import Mathlib.Tactic.FunProp.FunctionData
import Mathlib.Tactic.FunProp.RefinedDiscrTree
import Batteries.Data.RBMap.Alter
namespace Mathlib
open Lean Meta
namespace Meta.FunProp
inductive LambdaTheoremArgs
  | id
  | const
  | apply
  | comp (fArgId gArgId : Nat)
  | pi
  deriving Inhabited, BEq, Repr, Hashable
inductive LambdaTheoremType
  | id
  | const
  | apply
  | comp
  | pi
  deriving Inhabited, BEq, Repr, Hashable
def LambdaTheoremArgs.type (t : LambdaTheoremArgs) : LambdaTheoremType :=
  match t with
  | .id => .id
  | .const => .const
  | .comp .. => .comp
  | .apply  => .apply
  | .pi => .pi
def detectLambdaTheoremArgs (f : Expr) (ctxVars : Array Expr) :
    MetaM (Option LambdaTheoremArgs) := do
  let f ← forallTelescope (← inferType f) fun xs _ =>
    mkLambdaFVars xs (mkAppN f xs).headBeta
  match f with
  | .lam _ _ xBody _ =>
    unless xBody.hasLooseBVars do return .some .const
    match xBody with
    | .bvar 0 => return .some .id
    | .app (.bvar 0) (.fvar _) =>  return .some .apply
    | .app (.fvar fId) (.app (.fvar gId) (.bvar 0)) =>
      let .some argId_f := ctxVars.findIdx? (fun x => x == (.fvar fId)) | return none
      let .some argId_g := ctxVars.findIdx? (fun x => x == (.fvar gId)) | return none
      return .some <| .comp argId_f argId_g
    | .lam _ _ (.app (.app (.fvar _) (.bvar 1)) (.bvar 0)) _ =>
      return .some .pi
    | _ => return none
  | _ => return none
structure LambdaTheorem where
  funPropName : Name
  thmName : Name
  thmArgs : LambdaTheoremArgs
  deriving Inhabited, BEq
structure LambdaTheorems where
  theorems : Std.HashMap (Name × LambdaTheoremType) (Array LambdaTheorem) := {}
  deriving Inhabited
def LambdaTheorem.getProof (thm : LambdaTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName
abbrev LambdaTheoremsExt := SimpleScopedEnvExtension LambdaTheorem LambdaTheorems
initialize lambdaTheoremsExt : LambdaTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with theorems :=
        let es := d.theorems.getD (e.funPropName, e.thmArgs.type) #[]
        d.theorems.insert (e.funPropName, e.thmArgs.type) (es.push e)}
  }
def getLambdaTheorems (funPropName : Name) (type : LambdaTheoremType) :
    CoreM (Array LambdaTheorem) := do
  return (lambdaTheoremsExt.getState (← getEnv)).theorems.getD (funPropName,type) #[]
inductive TheoremForm where
  | uncurried | comp
  deriving Inhabited, BEq, Repr
instance : ToString TheoremForm :=
  ⟨fun x => match x with | .uncurried => "simple" | .comp => "compositional"⟩
structure FunctionTheorem where
  funPropName : Name
  thmOrigin   : Origin
  funOrigin   : Origin
  mainArgs    : Array Nat
  appliedArgs : Nat
  priority    : Nat  := eval_prio default
  form : TheoremForm
  deriving Inhabited, BEq
private local instance : Ord Name := ⟨Name.quickCmp⟩
structure FunctionTheorems where
  theorems :
    Batteries.RBMap Name (Batteries.RBMap Name (Array FunctionTheorem) compare) compare := {}
  deriving Inhabited
def FunctionTheorem.getProof (thm : FunctionTheorem) : MetaM Expr := do
  match thm.thmOrigin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => return .fvar id
abbrev FunctionTheoremsExt := SimpleScopedEnvExtension FunctionTheorem FunctionTheorems
initialize functionTheoremsExt : FunctionTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with
        theorems :=
          d.theorems.alter e.funOrigin.name fun funProperties =>
            let funProperties := funProperties.getD {}
            funProperties.alter e.funPropName fun thms =>
              let thms := thms.getD #[]
              thms.push e}
  }
def getTheoremsForFunction (funName : Name) (funPropName : Name) :
    CoreM (Array FunctionTheorem) := do
  return (functionTheoremsExt.getState (← getEnv)).theorems.findD funName {}
    |>.findD funPropName #[]
structure GeneralTheorem where
  funPropName   : Name
  thmName     : Name
  keys        : List RefinedDiscrTree.DTExpr
  priority    : Nat  := eval_prio default
  deriving Inhabited, BEq
def GeneralTheorem.getProof (thm : GeneralTheorem) : MetaM Expr := do
  mkConstWithFreshMVarLevels thm.thmName
structure GeneralTheorems where
  theorems     : RefinedDiscrTree GeneralTheorem := {}
  deriving Inhabited
abbrev GeneralTheoremsExt := SimpleScopedEnvExtension GeneralTheorem GeneralTheorems
initialize transitionTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (RefinedDiscrTree.insertDTExpr · · e) d.theorems}
  }
def getTransitionTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let ext := transitionTheoremsExt.getState (← getEnv)
  let candidates ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
    ext.theorems.getMatchWithScore e false
  let candidates := candidates.map (·.1) |>.flatten
  return candidates
initialize morTheoremsExt : GeneralTheoremsExt ←
  registerSimpleScopedEnvExtension {
    name     := by exact decl_name%
    initial  := {}
    addEntry := fun d e =>
      {d with theorems := e.keys.foldl (RefinedDiscrTree.insertDTExpr · · e) d.theorems}
  }
def getMorphismTheorems (e : Expr) : FunPropM (Array GeneralTheorem) := do
  let ext := morTheoremsExt.getState (← getEnv)
  let candidates ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
    ext.theorems.getMatchWithScore e false
  let candidates := candidates.map (·.1) |>.flatten
  return candidates
inductive Theorem where
  | lam        (thm : LambdaTheorem)
  | function   (thm : FunctionTheorem)
  | mor        (thm : GeneralTheorem)
  | transition (thm : GeneralTheorem)
def getTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM Theorem := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs b => do
    let .some (decl,f) ← getFunProp? b
      | throwError "unrecognized function property `{← ppExpr b}`"
    let funPropName := decl.funPropName
    let fData? ←
      withConfig (fun cfg => { cfg with zeta := false}) <| getFunctionData? f defaultUnfoldPred
    if let .some thmArgs ← detectLambdaTheoremArgs (← fData?.get) xs then
      return .lam {
        funPropName := funPropName
        thmName := declName
        thmArgs := thmArgs
      }
    let .data fData := fData?
      | throwError s!"function in invalid form {← ppExpr f}"
    match fData.fn with
    | .const funName _ =>
      let dec ← fData.nontrivialDecomposition
      let form : TheoremForm := if dec.isSome || funName == ``Prod.mk then .comp else .uncurried
      return .function {
        funPropName := funPropName
        thmOrigin := .decl declName
        funOrigin := .decl funName
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := prio
        form := form
      }
    | .fvar .. =>
      let (_,_,b') ← forallMetaTelescope info.type
      let keys := ← RefinedDiscrTree.mkDTExprs b' false
      let thm : GeneralTheorem := {
        funPropName := funPropName
        thmName := declName
        keys    := keys
        priority  := prio
      }
      match (← fData.isMorApplication) with
      | .exact => return .mor thm
      | .underApplied | .overApplied =>
        throwError "fun_prop theorem about morphism coercion has to be in fully applied form"
      | .none =>
        if fData.fn.isFVar && (fData.args.size == 1) &&
           (fData.args[0]!.expr == fData.mainVar) then
          return .transition thm
        throwError "Not a valid `fun_prop` theorem!"
    | _ =>
      throwError "unrecognized theoremType `{← ppExpr b}`"
def addTheorem (declName : Name) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  match (← getTheoremFromConst declName prio) with
  | .lam thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
lambda theorem: {thm.thmName}
function property: {thm.funPropName}
type: {repr thm.thmArgs.type}"
    lambdaTheoremsExt.add thm attrKind
  | .function thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
function theorem: {thm.thmOrigin.name}
function property: {thm.funPropName}
function name: {thm.funOrigin.name}
main arguments: {thm.mainArgs}
applied arguments: {thm.appliedArgs}
form: {toString thm.form} form"
    functionTheoremsExt.add thm attrKind
  | .mor thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
morphism theorem: {thm.thmName}
function property: {thm.funPropName}"
    morTheoremsExt.add thm attrKind
  | .transition thm =>
    trace[Meta.Tactic.fun_prop.attr] "\
transition theorem: {thm.thmName}
function property: {thm.funPropName}"
    transitionTheoremsExt.add thm attrKind
end Meta.FunProp
end Mathlib