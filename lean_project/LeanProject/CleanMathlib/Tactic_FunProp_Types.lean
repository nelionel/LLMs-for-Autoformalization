import Mathlib.Tactic.FunProp.FunctionData
import Batteries.Data.RBMap.Basic
namespace Mathlib
open Lean Meta
namespace Meta.FunProp
initialize registerTraceClass `Meta.Tactic.fun_prop
initialize registerTraceClass `Meta.Tactic.fun_prop.attr
initialize registerTraceClass `Debug.Meta.Tactic.fun_prop
inductive Origin where
  | decl (name : Name)
  | fvar (fvarId : FVarId)
  deriving Inhabited, BEq
def Origin.name (origin : Origin) : Name :=
  match origin with
  | .decl name => name
  | .fvar id => id.name
def Origin.getValue (origin : Origin) : MetaM Expr := do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)
def ppOrigin {m} [Monad m] [MonadEnv m] [MonadError m] : Origin → m MessageData
  | .decl n => return m!"{← mkConstWithLevelParams n}"
  | .fvar n => return mkFVar n
def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.name)
def FunctionData.getFnOrigin (fData : FunctionData) : Origin :=
  match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous
def defaultNamesToUnfold : Array Name :=
  #[`id, `Function.comp, `Function.HasUncurry.uncurry, `Function.uncurry]
structure Config where
  maxTransitionDepth := 1
  maxSteps := 100000
deriving Inhabited, BEq
structure Context where
  config : Config := {}
  constToUnfold : Batteries.RBSet Name Name.quickCmp :=
    .ofArray defaultNamesToUnfold _
  disch : Expr → MetaM (Option Expr) := fun _ => pure .none
  transitionDepth := 0
structure State where
  cache : Simp.Cache := {}
  failureCache : ExprSet := {}
  numSteps := 0
  msgLog : List String := []
def Context.increaseTransitionDepth (ctx : Context) : Context :=
  {ctx with transitionDepth := ctx.transitionDepth + 1}
abbrev FunPropM := ReaderT FunProp.Context <| StateT FunProp.State MetaM
structure Result where
  proof : Expr
def defaultUnfoldPred : Name → Bool :=
  defaultNamesToUnfold.contains
def unfoldNamePred : FunPropM (Name → Bool) := do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n
def increaseSteps : FunPropM Unit := do
  let numSteps := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})
def withIncreasedTransitionDepth {α} (go : FunPropM (Option α)) : FunPropM (Option α) := do
  let maxDepth := (← read).config.maxTransitionDepth
  let newDepth := (← read).transitionDepth + 1
  if newDepth > maxDepth then
    trace[Meta.Tactic.fun_prop]
   "maximum transition depth ({maxDepth}) reached
    if you want `fun_prop` to continue then increase the maximum depth with \
    `fun_prop (config := \{maxTransitionDepth := {newDepth}})`"
    return none
  else
    withReader (fun s => {s with transitionDepth := newDepth}) go
def logError (msg : String) : FunPropM Unit := do
  if (← read).transitionDepth = 0 then
    modify fun s =>
      {s with msgLog :=
        if s.msgLog.contains msg then
          s.msgLog
        else
          msg::s.msgLog}
end Meta.FunProp
end Mathlib