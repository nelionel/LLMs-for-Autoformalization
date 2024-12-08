import Mathlib.Tactic.CongrExclamation
open Lean Meta Elab Tactic
def Lean.MVarId.convert (e : Expr) (symm : Bool)
    (depth : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rcasesPat) := []) (g : MVarId) :
    MetaM (List MVarId) := g.withContext do
  let src ← inferType e
  let tgt ← g.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq (if symm then #[src, tgt] else #[tgt, src]))
  g.assign (← mkAppM (if symm then ``Eq.mp else ``Eq.mpr) #[v, e])
  let m := v.mvarId!
  m.congrN! depth config patterns
def Lean.MVarId.convertLocalDecl (g : MVarId) (fvarId : FVarId) (typeNew : Expr) (symm : Bool)
    (depth : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rcasesPat) := []) :
    MetaM (MVarId × List MVarId) := g.withContext do
  let typeOld ← fvarId.getType
  let v ← mkFreshExprMVar (← mkAppM ``Eq
    (if symm then #[typeNew, typeOld] else #[typeOld, typeNew]))
  let pf ← if symm then mkEqSymm v else pure v
  let res ← g.replaceLocalDecl fvarId typeNew pf
  let gs ← v.mvarId!.congrN! depth config patterns
  return (res.mvarId, gs)
namespace Mathlib.Tactic
syntax (name := convert) "convert" (Parser.Tactic.config)? " ←"? ppSpace term (" using " num)?
  (" with" (ppSpace colGt rintroPat)*)? : tactic
def elabTermForConvert (term : Syntax) (expectedType? : Option Expr) :
    TacticM (Expr × List MVarId) := do
  withCollectingNewGoalsFrom (parentTag := ← getMainTag) (tagSuffix := `convert)
      (allowNaturalHoles := true) do
    withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
      let t ← elabTermEnsuringType (mayPostpone := true) term expectedType?
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      return t
elab_rules : tactic
| `(tactic| convert $[$cfg:config]? $[←%$sym]? $term $[using $n]? $[with $ps?*]?) =>
  withMainContext do
    let config ← Congr!.elabConfig (mkOptionalNode cfg)
    let patterns := (Lean.Elab.Tactic.RCases.expandRIntroPats (ps?.getD #[])).toList
    let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
    let (e, gs) ← elabTermForConvert term expectedType
    liftMetaTactic fun g ↦
      return (← g.convert e sym.isSome (n.map (·.getNat)) config patterns) ++ gs
syntax (name := convertTo) "convert_to" (Parser.Tactic.config)? " ←"? ppSpace term (" using " num)?
  (" with" (ppSpace colGt rintroPat)*)? (Parser.Tactic.location)? : tactic
elab_rules : tactic
| `(tactic| convert_to $[$cfg:config]? $[←%$sym]? $newType $[using $n]?
    $[with $ps?*]? $[$loc?:location]?) => do
  let n : ℕ := n |>.map (·.getNat) |>.getD 1
  let config ← Congr!.elabConfig (mkOptionalNode cfg)
  let patterns := (Lean.Elab.Tactic.RCases.expandRIntroPats (ps?.getD #[])).toList
  withLocation (expandOptLocation (mkOptionalNode loc?))
    (atLocal := fun fvarId ↦ do
      let (e, gs) ← elabTermForConvert newType (← inferType (← fvarId.getType))
      liftMetaTactic fun g ↦ do
        let (g', gs') ← g.convertLocalDecl fvarId e sym.isSome n config patterns
        return (gs' ++ (g' :: gs)))
    (atTarget := do
      let expectedType ← mkFreshExprMVar (mkSort (← getLevel (← getMainTarget)))
      let (e, gs) ← elabTermForConvert (← `((id ?_ : $newType))) expectedType
      liftMetaTactic fun g ↦
        return (← g.convert e sym.isSome n config patterns) ++ gs)
    (failed := fun _ ↦ throwError "convert_to failed")
syntax (name := acChange) "ac_change " term (" using " num)? : tactic
macro_rules
| `(tactic| ac_change $t $[using $n]?) => `(tactic| convert_to $t:term $[using $n]? <;> try ac_rfl)
end Mathlib.Tactic