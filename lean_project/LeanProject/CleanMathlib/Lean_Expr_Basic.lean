import Mathlib.Init
import Lean.Meta.Tactic.Rewrite
import Batteries.Tactic.Alias
import Lean.Elab.Binders
namespace Lean
namespace BinderInfo
def brackets : BinderInfo → String × String
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strictImplicit => ("{{", "}}")
  | BinderInfo.instImplicit => ("[", "]")
  | _ => ("(", ")")
end BinderInfo
namespace Name
def mapPrefix (f : Name → Option Name) (n : Name) : Name := Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i
def fromComponents : List Name → Name := go .anonymous where
  go : Name → List Name → Name
  | n, []        => n
  | n, s :: rest => go (s.updatePrefix n) rest
def updateLast (f : String → String) : Name → Name
  | .str n s => .str n (f s)
  | n        => n
def lastComponentAsString : Name → String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""
@[deprecated (since := "2024-05-14")] alias getString := lastComponentAsString
def splitAt (nm : Name) (n : Nat) : Name × Name :=
  let (nm2, nm1) := nm.componentsRev.splitAt n
  (.fromComponents <| nm1.reverse, .fromComponents <| nm2.reverse)
def isPrefixOf? (pre nm : Name) : Option Name :=
  if pre == nm then
    some anonymous
  else match nm with
  | anonymous => none
  | num p' a => (isPrefixOf? pre p').map (·.num a)
  | str p' s => (isPrefixOf? pre p').map (·.str s)
open Meta
def isBlackListed {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
  pure <| declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName
end Name
namespace ConstantInfo
def isDef : ConstantInfo → Bool
  | defnInfo _ => true
  | _          => false
def isThm : ConstantInfo → Bool
  | thmInfo _ => true
  | _          => false
def updateConstantVal : ConstantInfo → ConstantVal → ConstantInfo
  | defnInfo   info, v => defnInfo   {info with toConstantVal := v}
  | axiomInfo  info, v => axiomInfo  {info with toConstantVal := v}
  | thmInfo    info, v => thmInfo    {info with toConstantVal := v}
  | opaqueInfo info, v => opaqueInfo {info with toConstantVal := v}
  | quotInfo   info, v => quotInfo   {info with toConstantVal := v}
  | inductInfo info, v => inductInfo {info with toConstantVal := v}
  | ctorInfo   info, v => ctorInfo   {info with toConstantVal := v}
  | recInfo    info, v => recInfo    {info with toConstantVal := v}
def updateName (c : ConstantInfo) (name : Name) : ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with name}
def updateType (c : ConstantInfo) (type : Expr) : ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with type}
def updateLevelParams (c : ConstantInfo) (levelParams : List Name) :
    ConstantInfo :=
  c.updateConstantVal {c.toConstantVal with levelParams}
def updateValue : ConstantInfo → Expr → ConstantInfo
  | defnInfo   info, v => defnInfo   {info with value := v}
  | thmInfo    info, v => thmInfo    {info with value := v}
  | opaqueInfo info, v => opaqueInfo {info with value := v}
  | d, _ => d
def toDeclaration! : ConstantInfo → Declaration
  | defnInfo   info => Declaration.defnDecl info
  | thmInfo    info => Declaration.thmDecl     info
  | axiomInfo  info => Declaration.axiomDecl   info
  | opaqueInfo info => Declaration.opaqueDecl  info
  | quotInfo   _ => panic! "toDeclaration for quotInfo not implemented"
  | inductInfo _ => panic! "toDeclaration for inductInfo not implemented"
  | ctorInfo   _ => panic! "toDeclaration for ctorInfo not implemented"
  | recInfo    _ => panic! "toDeclaration for recInfo not implemented"
end ConstantInfo
open Meta
def mkConst' (constName : Name) : MetaM Expr := do
  return mkConst constName (← (← getConstInfo constName).levelParams.mapM fun _ => mkFreshLevelMVar)
namespace Expr
def bvarIdx? : Expr → Option Nat
  | bvar idx => some idx
  | _        => none
private def getAppAppsAux : Expr → Array Expr → Nat → Array Expr
  | .app f a, as, i => getAppAppsAux f (as.set! i (.app f a)) (i-1)
  | _,       as, _ => as
@[inline]
def getAppApps (e : Expr) : Array Expr :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppAppsAux e (mkArray nargs dummy) (nargs-1)
def eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform (skipConstInApp := true) e
    (pre := fun e => do
      if (← Meta.isProof e) then
        return .continue (← mkSyntheticSorry (← inferType e))
      else
        return .continue)
def fvarId? : Expr → Option FVarId
  | .fvar n => n
  | _ => none
def type? : Expr → Option Level
  | .sort u => u.dec
  | _ => none
def isConstantApplication (e : Expr) :=
  e.isApp && aux e.getAppNumArgs'.pred e.getAppFn' e.getAppNumArgs'
where
  aux (depth : Nat) : Expr → Nat → Bool
    | .lam _ _ b _, n + 1  => aux depth b n
    | e, 0  => !e.hasLooseBVar (depth - 1)
    | _, _ => false
def letDepth : Expr → Nat
  | .letE _ _ _ b _ => b.letDepth + 1
  | _ => 0
open Meta
def ensureHasNoMVars (e : Expr) : MetaM Unit := do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "tactic failed, resulting expression contains metavariables{indentExpr e}"
def ofNat (α : Expr) (n : Nat) : MetaM Expr := do
  mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit n, none]
def ofInt (α : Expr) : Int → MetaM Expr
  | Int.ofNat n => Expr.ofNat α n
  | Int.negSucc n => do mkAppM ``Neg.neg #[← Expr.ofNat α (n+1)]
section recognizers
partial def numeral? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then n
  else
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none
def zero? (e : Expr) : Bool :=
  match e.numeral? with
  | some 0 => true
  | _ => false
def ne?' (e : Expr) : Option (Expr × Expr × Expr) :=
  e.ne? <|> (e.not? >>= Expr.eq?)
@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LE.le
  return (type, lhs, rhs)
@[inline] def lt? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  return (type, lhs, rhs)
def sides? (ty : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if let some (lhs, rhs) := ty.iff? then
    some (.sort .zero, lhs, .sort .zero, rhs)
  else if let some (ty, lhs, rhs) := ty.eq? then
    some (ty, lhs, ty, rhs)
  else
    ty.heq?
end recognizers
universe u
def modifyAppArgM {M : Type → Type u} [Functor M] [Pure M]
    (modifier : Expr → M Expr) : Expr → M Expr
  | app f a => mkApp f <$> modifier a
  | e => pure e
def modifyRevArg (modifier : Expr → Expr) : Nat → Expr → Expr
  | 0,     (.app f x) => .app f (modifier x)
  | (i+1), (.app f x) => .app (modifyRevArg modifier i f) x
  | _, e => e
def modifyArg (modifier : Expr → Expr) (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Expr :=
  modifyRevArg modifier (n - i - 1) e
def setArg (e : Expr) (i : Nat) (x : Expr) (n := e.getAppNumArgs) : Expr :=
  e.modifyArg (fun _ => x) i n
def getRevArg? : Expr → Nat → Option Expr
  | app _ a, 0   => a
  | app f _, i+1 => getRevArg! f i
  | _,       _   => none
def getArg? (e : Expr) (i : Nat) (n := e.getAppNumArgs) : Option Expr :=
  getRevArg? e (n - i - 1)
def modifyArgM {M : Type → Type u} [Monad M] (modifier : Expr → M Expr)
    (e : Expr) (i : Nat) (n := e.getAppNumArgs) : M Expr := do
  let some a := getArg? e i | return e
  let a ← modifier a
  return modifyArg (fun _ ↦ a) e i n
def renameBVar (e : Expr) (old new : Name) : Expr :=
  match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | e => e
open Lean.Meta in
def getBinderName (e : Expr) : MetaM (Option Name) := do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none
open Lean.Elab.Term
def addLocalVarInfoForBinderIdent (fvar : Expr) (tk : TSyntax ``binderIdent) : MetaM Unit :=
  discard <| TermElabM.run do
    match tk with
    | `(binderIdent| $n:ident) => Elab.Term.addLocalVarInfo n fvar
    | tk => Elab.Term.addLocalVarInfo (Unhygienic.run `(_%$tk)) fvar
def mkDirectProjection (e : Expr) (fieldName : Name) : MetaM Expr := do
  let type ← whnf (← inferType e)
  let .const structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
  let some projName := getProjFnForField? (← getEnv) structName fieldName |
    throwError "{structName} doesn't have field {fieldName}"
  return mkAppN (.const projName us) (type.getAppArgs.push e)
def mkProjection (e : Expr) (fieldName : Name) : MetaM Expr := do
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let some baseStruct := findField? (← getEnv) structName fieldName |
    throwError "No parent of {structName} has field {fieldName}"
  let mut e := e
  for projName in (getPathToBaseStructure? (← getEnv) baseStruct structName).get! do
    let type ← whnf (← inferType e)
    let .const _structName us := type.getAppFn | throwError "{e} doesn't have a structure as type"
    e := mkAppN (.const projName us) (type.getAppArgs.push e)
  mkDirectProjection e fieldName
def reduceProjStruct? (e : Expr) : MetaM (Option Expr) := do
  let .const cname _ := e.getAppFn | return none
  let some pinfo ← getProjectionFnInfo? cname | return none
  let args := e.getAppArgs
  if ha : args.size = pinfo.numParams + 1 then
    let sarg := args[pinfo.numParams]'(ha ▸ pinfo.numParams.lt_succ_self)
    unless sarg.getAppFn.isConstOf pinfo.ctorName do
      return none
    let sfields := sarg.getAppArgs
    let sidx := pinfo.numParams + pinfo.i
    if hs : sidx < sfields.size then
      return some (sfields[sidx]'hs)
    else
      throwError m!"ill-formed expression, {cname} is the {pinfo.i + 1}-th projection function \
        but {sarg} does not have enough arguments"
  else
    return none
def containsConst (e : Expr) (p : Name → Bool) : Bool :=
  Option.isSome <| e.find? fun | .const n _ => p n | _ => false
def rewrite (e eq : Expr) : MetaM Expr := do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'
def rewriteType (e eq : Expr) : MetaM Expr := do
  mkEqMP (← (← inferType e).rewrite eq) e
partial def forallNot_of_notExists (ex hNotEx : Expr) : MetaM (Expr × Expr) := do
  let .app (.app (.const ``Exists [lvl]) A) p := ex | failure
  go lvl A p hNotEx
where
  go (lvl : Level) (A p hNotEx : Expr) : MetaM (Expr × Expr) := do
    let xn ← mkFreshUserName `x
    withLocalDeclD xn A fun x => do
      let px := p.beta #[x]
      let notPx := mkNot px
      let hAllNotPx := mkApp3 (.const ``forall_not_of_not_exists [lvl]) A p hNotEx
      if let .app (.app (.const ``Exists [lvl']) A') p' := px then
        let hNotPxN ← mkFreshUserName `h
        withLocalDeclD hNotPxN notPx fun hNotPx => do
          let (qx, hQx) ← go lvl' A' p' hNotPx
          let allQx ← mkForallFVars #[x] qx
          let hNotPxImpQx ← mkLambdaFVars #[hNotPx] hQx
          let hAllQx ← mkLambdaFVars #[x] (.app hNotPxImpQx (.app hAllNotPx x))
          return (allQx, hAllQx)
      else
        let allNotPx ← mkForallFVars #[x] notPx
        return (allNotPx, hAllNotPx)
end Expr
def getFieldsToParents (env : Environment) (structName : Name) : Array Name :=
  getStructureFields env structName |>.filter fun fieldName =>
    isSubobjectField? env structName fieldName |>.isSome
end Lean