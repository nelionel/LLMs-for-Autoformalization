import Mathlib.Init
import Lean.Elab.Tactic.Conv.Pattern
namespace Lean.MVarId
partial def casesMatching (matcher : Expr → MetaM Bool) (recursive := false) (allowSplit := true)
    (throwOnNoMatch := true) (g : MVarId) : MetaM (List MVarId) := do
  let result := (← go g).toList
  if throwOnNoMatch && result == [g] then
    throwError "no match"
  else
    return result
  where
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if ← matcher ldecl.type then
          let mut acc := acc
          let subgoals ← if allowSplit then
            g.cases ldecl.fvarId
          else
            let s ← saveState
            let subgoals ← g.cases ldecl.fvarId
            if subgoals.size > 1 then
              s.restore
              continue
            else
              pure subgoals
          for subgoal in subgoals do
            if recursive then
              acc ← go subgoal.mvarId acc
            else
              acc := acc.push subgoal.mvarId
          return acc
      return (acc.push g)
def casesType (heads : Array Name) (recursive := false) (allowSplit := true) :
    MVarId → MetaM (List MVarId) :=
  let matcher ty := pure <|
    if let .const n .. := ty.headBeta.getAppFn then heads.contains n else false
  casesMatching matcher recursive allowSplit
end Lean.MVarId
namespace Mathlib.Tactic
open Lean Meta Elab Tactic MVarId
def elabPatterns (pats : Array Term) : TermElabM (Array AbstractMVarsResult) :=
  withTheReader Term.Context (fun ctx ↦ { ctx with ignoreTCFailures := true }) <|
  Term.withoutErrToSorry <|
  pats.mapM fun p ↦ Term.withoutModifyingElabMetaStateWithInfo do
    withRef p <| abstractMVars (← Term.elabTerm p none)
def matchPatterns (pats : Array AbstractMVarsResult) (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  pats.anyM fun p ↦ return (← Conv.matchPattern? p e) matches some (_, #[])
elab (name := casesM) "casesm" recursive:"*"? ppSpace pats:term,+ : tactic => do
  let pats ← elabPatterns pats.getElems
  liftMetaTactic (casesMatching (matchPatterns pats) recursive.isSome)
def elabCasesType (heads : Array Ident)
    (recursive := false) (allowSplit := true) : TacticM Unit := do
  let heads ← heads.mapM (fun stx => realizeGlobalConstNoOverloadWithInfo stx)
  liftMetaTactic (casesType heads recursive allowSplit)
elab (name := casesType) "cases_type" recursive:"*"? heads:(ppSpace colGt ident)+ : tactic =>
  elabCasesType heads recursive.isSome true
@[inherit_doc casesType]
elab (name := casesType!) "cases_type!" recursive:"*"? heads:(ppSpace colGt ident)+ : tactic =>
  elabCasesType heads recursive.isSome false
partial def constructorMatching (g : MVarId) (matcher : Expr → MetaM Bool)
    (recursive := false) (throwOnNoMatch := true) : MetaM (List MVarId) := do
  let result ←
    (if recursive then (do
      let result ← go g
      pure result.toList)
     else
      (g.withContext do
          if ← matcher (← g.getType) then g.constructor else pure [g]))
  if throwOnNoMatch && [g] == result then
    throwError "no match"
  else
    return result
where
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      if ← matcher (← g.getType) then
        let mut acc := acc
        for g' in ← g.constructor do
          acc ← go g' acc
        return acc
      return (acc.push g)
elab (name := constructorM) "constructorm" recursive:"*"? ppSpace pats:term,+ : tactic => do
  let pats ← elabPatterns pats.getElems
  liftMetaTactic (constructorMatching · (matchPatterns pats) recursive.isSome)
end Mathlib.Tactic