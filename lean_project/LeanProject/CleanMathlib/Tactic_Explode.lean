import Lean.Elab.Command
import Lean.PrettyPrinter
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty
set_option linter.unusedVariables false
open Lean
namespace Mathlib.Explode
variable (select : Expr → MetaM Bool) (includeAllDeps : Bool) in
partial def explodeCore (e : Expr) (depth : Nat) (entries : Entries) (start : Bool := false) :
    MetaM (Option Entry × Entries) := do
  trace[explode] "depth = {depth}, start = {start}, e = {e}"
  let e := e.cleanupAnnotations
  if let some entry := entries.find? e then
    trace[explode] "already seen"
    return (entry, entries)
  if !(← select e) then
    trace[explode] "filtered out"
    return (none, entries)
  match e with
  | .lam .. => do
    trace[explode] ".lam"
    Meta.lambdaTelescope e fun args body => do
      let mut entries' := entries
      let mut rdeps := []
      for arg in args, i in [0:args.size] do
        let (argEntry, entries'') := entries'.add arg
          { type     := ← addMessageContext <| ← Meta.inferType arg
            depth    := depth
            status   :=
              if start
              then Status.sintro
              else if i == 0 then Status.intro else Status.cintro
            thm      := ← addMessageContext <| arg
            deps     := []
            useAsDep := ← select arg }
        entries' := entries''
        rdeps := some argEntry.line! :: rdeps
      let (bodyEntry?, entries) ←
        explodeCore body (if start then depth else depth + 1) entries'
      rdeps := consDep bodyEntry? rdeps
      let (entry, entries) := entries.add e
        { type     := ← addMessageContext <| ← Meta.inferType e
          depth    := depth
          status   := Status.lam
          thm      := "∀I" 
          deps     := rdeps.reverse
          useAsDep := true }
      return (entry, entries)
  | .app .. => do
    trace[explode] ".app"
    let fn := e.getAppFn
    let args := e.getAppArgs
    let (fnEntry?, entries) ←
      if fn.isConst then
        pure (none, entries)
      else
        explodeCore fn depth entries
    let deps := if fn.isConst then [] else consDep fnEntry? []
    let mut entries' := entries
    let mut rdeps := []
    for arg in args do
      let (appEntry?, entries'') ← explodeCore arg depth entries'
      entries' := entries''
      rdeps := consDep appEntry? rdeps
    let deps := deps ++ rdeps.reverse
    let (entry, entries) := entries'.add e
      { type     := ← addMessageContext <| ← Meta.inferType e
        depth    := depth
        status   := Status.reg
        thm      := ← addMessageContext <| if fn.isConst then MessageData.ofConst fn else "∀E"
        deps     := deps
        useAsDep := true }
    return (entry, entries)
  | .letE varName varType val body _ => do
    trace[explode] ".letE"
    let varType := varType.cleanupAnnotations
    Meta.withLocalDeclD varName varType fun var => do
      let (valEntry?, entries) ← explodeCore val depth entries
      let entries := valEntry?.map (entries.addSynonym var) |>.getD entries
      explodeCore (body.instantiate1 var) depth entries
  | _ => do
    trace[explode] ".{e.ctorName} (default handler)"
    let (entry, entries) := entries.add e
      { type     := ← addMessageContext <| ← Meta.inferType e
        depth    := depth
        status   := Status.reg
        thm      := ← addMessageContext e
        deps     := []
        useAsDep := ← select e }
    return (entry, entries)
where
  consDep (entry? : Option Entry) (deps : List (Option Nat)) : List (Option Nat) :=
    if let some entry := entry? then
      if includeAllDeps || entry.useAsDep then entry.line! :: deps else deps
    else
      deps
def explode (e : Expr) (filterProofs : Bool := true) : MetaM Entries := do
  let filter (e : Expr) : MetaM Bool :=
    if filterProofs then Meta.isProof e else return true
  let (_, entries) ← explodeCore (start := true) filter false e 0 default
  return entries
open Elab in
elab "#explode " stx:term : command => withoutModifyingEnv <| Command.runTermElabM fun _ => do
  let (heading, e) ← try
    let theoremName : Name ← realizeGlobalConstNoOverloadWithInfo stx
    addCompletionInfo <| .id stx theoremName (danglingDot := false) {} none
    let decl ← getConstInfo theoremName
    let c : Expr := .const theoremName (decl.levelParams.map mkLevelParam)
    pure (m!"{MessageData.ofConst c} : {decl.type}", decl.value!)
  catch _ =>
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    pure (m!"{e} : {← Meta.inferType e}", e)
  unless e.isSyntheticSorry do
    let entries ← explode e
    let fitchTable : MessageData ← entriesToMessageData entries
    logInfo <|← addMessageContext m!"{heading}\n\n{fitchTable}\n"
end Explode
end Mathlib