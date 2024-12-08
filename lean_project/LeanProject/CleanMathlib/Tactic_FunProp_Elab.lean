import Mathlib.Tactic.FunProp.Core
namespace Mathlib
open Lean Meta Elab Tactic
namespace Meta.FunProp
open Lean.Parser.Tactic
declare_config_elab elabFunPropConfig FunProp.Config
syntax (name := funPropTacStx)
  "fun_prop" optConfig (discharger)? (" [" withoutPosition(ident,*,?) "]")? : tactic
private def emptyDischarge : Expr → MetaM (Option Expr) :=
  fun e =>
    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] discharging: {← ppExpr e}") do
      pure none
@[tactic funPropTacStx]
def funPropTac : Tactic
  | `(tactic| fun_prop $cfg:optConfig $[$d]? $[[$names,*]]?) => do
    let goal ← getMainGoal
    goal.withContext do
      let goalType ← goal.getType
      withReducible <| forallTelescopeReducing (← whnfR goalType) fun _ type => do
        unless (← getFunProp? type).isSome do
          let hint :=
            if let .some n := type.getAppFn.constName?
            then s!" Maybe you forgot marking `{n}` with `@[fun_prop]`."
            else ""
          throwError "`{← ppExpr type}` is not a `fun_prop` goal!{hint}"
      let cfg ← elabFunPropConfig cfg
      let disch ← show MetaM (Expr → MetaM (Option Expr)) from do
        match d with
        | none => pure emptyDischarge
        | some d =>
          match d with
          | `(discharger| (discharger:=$tac)) => pure <| tacticToDischarge (← `(tactic| ($tac)))
          | _ => pure emptyDischarge
      let namesToUnfold : Array Name :=
        match names with
        | none => #[]
        | .some ns => ns.getElems.map (fun n => n.getId)
      let namesToUnfold := namesToUnfold.append defaultNamesToUnfold
      let ctx : Context :=
        { config := cfg,
          disch := disch
          constToUnfold := .ofArray namesToUnfold _}
      let (r?, s) ← funProp goalType ctx |>.run {}
      if let .some r := r? then
        goal.assign r.proof
      else
        let mut msg := s!"`fun_prop` was unable to prove `{← Meta.ppExpr goalType}`\n\n"
        msg := msg ++ "Issues:"
        msg := s.msgLog.foldl (init := msg) (fun msg m => msg ++ "\n  " ++ m)
        throwError msg
  | _ => throwUnsupportedSyntax
elab "#print_fun_prop_theorems " funIdent:ident funProp:(ident)? : command => do
  let funName ← ensureNonAmbiguous funIdent (← resolveGlobalConst funIdent)
  let funProp? ← funProp.mapM (fun stx => do
    ensureNonAmbiguous stx (← resolveGlobalConst stx))
  let theorems := (functionTheoremsExt.getState (← getEnv)).theorems.findD funName {}
  let logTheorems (funProp : Name) (thms : Array FunctionTheorem) : Command.CommandElabM Unit := do
    let mut msg : MessageData := ""
    msg := msg ++ m!"{← Meta.ppOrigin (.decl funProp)}"
    for thm in thms do
      msg := msg ++ m!"\n  {← Meta.ppOrigin (.decl thm.thmOrigin.name)}, \
                 args: {thm.mainArgs}, form: {thm.form}"
      pure ()
    logInfo msg
  match funProp? with
  | none =>
    for (funProp,thms) in theorems do
      logTheorems funProp thms
  | some funProp =>
    logTheorems funProp (theorems.findD funProp #[])
end Meta.FunProp
end Mathlib