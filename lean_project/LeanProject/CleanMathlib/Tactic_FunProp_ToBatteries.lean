import Mathlib.Init
namespace Mathlib
open Lean Meta
namespace Meta.FunProp
def isOrderedSubsetOf {α} [Inhabited α] [DecidableEq α] (a b : Array α) : Bool :=
  Id.run do
  if a.size > b.size then
    return false
  let mut i := 0
  for j in [0:b.size] do
    if i = a.size then
      break
    if a[i]! = b[j]! then
      i := i+1
  if i = a.size then
    return true
  else
    return false
private def letTelescopeImpl {α} (e : Expr) (k : Array Expr → Expr → MetaM α) :
    MetaM α :=
  lambdaLetTelescope e fun xs b ↦ do
    if let .some i ← xs.findIdxM? (fun x ↦ do pure !(← x.fvarId!.isLetVar)) then
      k xs[0:i] (← mkLambdaFVars xs[i:] b)
    else
      k xs b
def letTelescope {α n} [MonadControlT MetaM n] [Monad n] (e : Expr)
    (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => letTelescopeImpl e k) k
def _root_.Lean.Expr.swapBVars (e : Expr) (i j : Nat) : Expr :=
  let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a
  e.instantiate swapBVarArray
def mkProdElem (xs : Array Expr) : MetaM Expr := do
  match xs.size with
  | 0 => return default
  | 1 => return xs[0]!
  | _ =>
    let n := xs.size
    xs[0:n-1].foldrM (init := xs[n-1]!) fun x p => mkAppM ``Prod.mk #[x,p]
def mkProdProj (x : Expr) (i : Nat) (n : Nat) : MetaM Expr := do
  match i, n with
  | _, 0 => pure x
  | _, 1 => pure x
  | 0, _ => mkAppM ``Prod.fst #[x]
  | i'+1, n'+1 => mkProdProj (← withTransparency .all <| mkAppM ``Prod.snd #[x]) i' n'
def mkProdSplitElem (xs : Expr) (n : Nat) : MetaM (Array Expr) :=
  (Array.range n)
    |>.mapM (fun i ↦ mkProdProj xs i n)
def mkUncurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallBoundedTelescope (← inferType f) n fun xs _ ↦ do
    let xProdName : String ← xs.foldlM (init:="") fun n x ↦
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs)
    withLocalDecl (.mkSimple xProdName) default xProdType fun xProd ↦ do
      let xs' ← mkProdSplitElem xProd n
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta
def etaExpand1 (f : Expr) : MetaM Expr := do
  let f := f.eta
  if f.isLambda then
    return f
  else
    withDefault do forallBoundedTelescope (← inferType f) (.some 1) fun xs _ => do
      mkLambdaFVars xs (mkAppN f xs)
private def betaThroughLetAux (f : Expr) (args : List Expr) : Expr :=
  match f, args with
  | f, [] => f
  | .lam _ _ b _, a :: as => (betaThroughLetAux (b.instantiate1 a) as)
  | .letE n t v b _, args => .letE n t v (betaThroughLetAux b args) false
  | .mdata _ b, args => betaThroughLetAux b args
  | f, args => mkAppN f args.toArray
def betaThroughLet (f : Expr) (args : Array Expr) : Expr :=
  betaThroughLetAux f args.toList
def headBetaThroughLet (e : Expr) : Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn true then betaThroughLet f e.getAppArgs else e
end Meta.FunProp
end Mathlib