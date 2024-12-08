import Mathlib.Init
import Batteries.Util.Cache
import Lean.HeadIndex
import Lean.Elab.Command
open Lean Std
open Lean.Meta
open Lean.Elab
open Lean.Elab
open Batteries.Tactic
namespace Mathlib.Tactic.Find
private partial def matchHyps : List Expr → List Expr → List Expr → MetaM Bool
  | p::ps, oldHyps, h::newHyps => do
    let pt ← inferType p
    let t ← inferType h
    if (← isDefEq pt t) then
      matchHyps ps [] (oldHyps ++ newHyps)
    else
      matchHyps (p::ps) (h::oldHyps) newHyps
  | [], _, _    => pure true
  | _::_, _, [] => pure false
private def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  pure <| declName.isInternal
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName
  <||> isMatcher declName
initialize findDeclsPerHead : DeclCache (Std.HashMap HeadIndex (Array Name)) ←
  DeclCache.mk "#find: init cache" failure {} fun _ c headMap ↦ do
    if (← isBlackListed c.name) then
      return headMap
    let (_, _, ty) ← forallMetaTelescopeReducing c.type
    let head := ty.toHeadIndex
    pure <| headMap.insert head (headMap.getD head #[] |>.push c.name)
def findType (t : Expr) : TermElabM Unit := withReducible do
  let t ← instantiateMVars t
  let head := (← forallMetaTelescopeReducing t).2.2.toHeadIndex
  let pat ← abstractMVars t
  let env ← getEnv
  let mut numFound := 0
  for n in (← findDeclsPerHead.get).getD head #[] do
    let c := env.find? n |>.get!
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    let found ← forallTelescopeReducing cTy fun cParams cTy' ↦ do
      let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
        (← mkFreshLevelMVars pat.numMVars).toArray
      let (_, _, pat) ← lambdaMetaTelescope pat
      let (patParams, _, pat) ← forallMetaTelescopeReducing pat
      isDefEq cTy' pat <&&> matchHyps patParams.toList [] cParams.toList
    if found then
      numFound := numFound + 1
      if numFound > 20 then
        logInfo m!"maximum number of search results reached"
        break
      logInfo m!"{n}: {cTy}"
open Lean.Elab.Command in
elab "#find " t:term : command =>
  liftTermElabM do
    let t ← Term.elabTerm t none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    findType t
open Lean.Elab.Tactic
elab "find" : tactic => do
  findType (← getMainTarget)
elab "#find " t:term : tactic => do
  let t ← Term.elabTerm t none
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  findType t
end Mathlib.Tactic.Find