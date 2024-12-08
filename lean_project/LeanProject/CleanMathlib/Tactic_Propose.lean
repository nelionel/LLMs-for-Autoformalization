import Lean.Meta.Tactic.TryThis
import Lean.Meta.Tactic.SolveByElim
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Meta
import Mathlib.Lean.Meta.Basic
import Batteries.Util.Cache
import Mathlib.Tactic.Core
namespace Mathlib.Tactic.Propose
open Lean Meta Batteries.Tactic Tactic.TryThis
initialize registerTraceClass `Tactic.propose
initialize proposeLemmas : DeclCache (DiscrTree Name) ←
  DeclCache.mk "have?: init cache" failure {} fun name constInfo lemmas => do
    if constInfo.isUnsafe then return lemmas
    if ← name.isBlackListed then return lemmas
    withNewMCtxDepth do withReducible do
      let (mvars, _, _) ← forallMetaTelescope constInfo.type
      let mut lemmas := lemmas
      for m in mvars do
        lemmas ← lemmas.insertIfSpecific (← inferType m) name
      pure lemmas
open Lean.Meta.SolveByElim in
def solveByElim (orig : MVarId) (goals : Array MVarId) (use : Array Expr) (required : Array Expr)
    (depth) := do
  let cfg : SolveByElimConfig :=
    { maxDepth := depth, exfalso := true, symm := true, intro := false }
  let cfg := if !required.isEmpty then
    cfg.testSolutions (fun _ => do
    let r ← instantiateMVars (.mvar orig)
    pure <| required.all fun e => e.occurs r)
  else
    cfg
  let cfg := cfg.synthInstance
  _ ← SolveByElim.solveByElim
    cfg (use.toList.map pure) (fun _ => return (← getLocalHyps).toList) goals.toList
def propose (lemmas : DiscrTree Name) (type : Expr) (required : Array Expr)
    (solveByElimDepth := 15) : MetaM (Array (Name × Expr)) := do
  guard !required.isEmpty
  let ty ← whnfR (← instantiateMVars (← inferType required[0]!))
  let candidates ← lemmas.getMatch ty
  candidates.filterMapM fun lem : Name =>
    try
      trace[Tactic.propose] "considering {lem}"
      let Expr.mvar g ← mkFreshExprMVar type | failure
      let e ← mkConstWithFreshMVarLevels lem
      let (args, _, _) ← forallMetaTelescope (← inferType e)
      let .true ← preservingMCtx <| withAssignableSyntheticOpaque <|
        isDefEq type (← inferType (mkAppN e args)) | failure
      g.assign (mkAppN e args)
      let use := required.filterMap fun e => match e with | .fvar _ => none | _ => some e
      solveByElim g (args.map fun a => a.mvarId!) use required solveByElimDepth
      trace[Tactic.propose] "successfully filled in arguments for {lem}"
      pure <| some (lem, ← instantiateMVars (.mvar g))
    catch _ => pure none
open Lean.Parser.Tactic
syntax (name := propose') "have?" "!"? (ident)? (" : " term)? " using " (colGt term),+ : tactic
open Elab.Tactic Elab Tactic in
elab_rules : tactic
  | `(tactic| have?%$tk $[!%$lucky]? $[$h:ident]? $[ : $type:term]? using $[$terms:term],*) => do
    let stx ← getRef
    let goal ← getMainGoal
    goal.withContext do
      let required ← terms.mapM (elabTerm · none)
      let type ← match type with
      | some stx => elabTermWithHoles stx none (← getMainTag) true <&> (·.1)
      | none => mkFreshTypeMVar
      let proposals ← propose (← proposeLemmas.get) type required
      if proposals.isEmpty then
        throwError "propose could not find any lemmas using the given hypotheses"
      for p in proposals.toList.take 10 do
        addHaveSuggestion tk (h.map (·.getId)) (← inferType p.2) p.2 stx
      if lucky.isSome then
        let mut g := goal
        for p in proposals.toList.take 10 do
          (_, g) ← g.let p.1 p.2
        replaceMainGoal [g]
@[inherit_doc propose'] syntax "have?!" (" : " term)? " using " (colGt term),+ : tactic
@[inherit_doc propose'] syntax "have!?" (" : " term)? " using " (colGt term),+ : tactic
macro_rules
  | `(tactic| have?!%$tk $[: $type]? using $terms,*) =>
    `(tactic| have?%$tk ! $[: $type]? using $terms,*)
  | `(tactic| have!?%$tk $[: $type]? using $terms,*) =>
    `(tactic| have?%$tk ! $[: $type]? using $terms,*)
end Mathlib.Tactic.Propose