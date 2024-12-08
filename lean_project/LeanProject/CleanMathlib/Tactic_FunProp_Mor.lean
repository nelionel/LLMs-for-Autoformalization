import Mathlib.Data.FunLike.Basic
import Mathlib.Tactic.FunProp.ToBatteries
namespace Mathlib
open Lean Meta
namespace Meta.FunProp
namespace Mor
def isCoeFunName (name : Name) : CoreM Bool := do
  let .some info ← getCoeFnInfo? name | return false
  return info.type == .coeFun
def isCoeFun (e : Expr) : MetaM Bool := do
  let .some (name,_) := e.getAppFn.const? | return false
  let .some info ← getCoeFnInfo? name | return false
  return e.getAppNumArgs' + 1 == info.numArgs
structure App where
  coe : Expr
  fn  : Expr
  arg : Expr
def isMorApp? (e : Expr) : MetaM (Option App) := do
  let .app (.app coe f) x := e | return none
  if ← isCoeFun coe then
    return .some { coe := coe, fn := f, arg := x }
  else
    return none
partial def whnfPred (e : Expr) (pred : Expr → MetaM Bool) :
    MetaM Expr := do
  whnfEasyCases e fun e => do
    let e ← whnfCore e
    if let .some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← whnfPred f pred
      if (← getConfig).zeta then
        return (coe.app f).app x
      else
        return ← letTelescope f fun xs f' =>
          mkLambdaFVars xs ((coe.app f').app x)
    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => whnfPred e pred
        | none   => return e
    else
      return e
def whnf (e : Expr) : MetaM Expr :=
  whnfPred e (fun _ => return false)
structure Arg where
  expr : Expr
  coe : Option Expr := none
  deriving Inhabited
def app (f : Expr) (arg : Arg) : Expr :=
  match arg.coe with
  | .none => f.app arg.expr
  | .some coe => (coe.app f).app arg.expr
partial def withApp {α} (e : Expr) (k : Expr → Array Arg → MetaM α) : MetaM α :=
  go e #[]
where
  go : Expr → Array Arg →  MetaM α
    | .mdata _ b, as => go b as
    | .app (.app c f) x, as => do
      if ← isCoeFun c then
        go f (as.push { coe := c, expr := x})
      else
        go (.app c f) (as.push { expr := x})
    | .app (.proj n i f) x, as => do
      let env ← getEnv
      let info := getStructureInfo? env n |>.get!
      let projFn := getProjFnForField? env n (info.fieldNames[i]!) |>.get!
      let .app c f ← mkAppM projFn #[f] | panic! "bug in Mor.withApp"
      go (.app (.app c f) x) as
    | .app f a, as =>
      go f (as.push { expr := a })
    | f        , as => k f as.reverse
def getAppFn (e : Expr) : MetaM Expr :=
  match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ => do
    if ← isCoeFun c then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => return e
def getAppArgs (e : Expr) : MetaM (Array Arg) := withApp e fun _ xs => return xs
def mkAppN (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, .some coe⟩ => (coe.app f).app x)
end Mor
end Meta.FunProp
end Mathlib