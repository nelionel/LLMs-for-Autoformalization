import Mathlib.Control.Basic
import Mathlib.Tactic.Linarith.Verification
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm
import Mathlib.Tactic.Ring.Basic
open Lean Elab Tactic Meta
open Batteries Mathlib
namespace Linarith
section
open Meta
structure LinarithConfig : Type where
  discharger : TacticM Unit := do evalTactic (← `(tactic| ring1))
  exfalso : Bool := true
  transparency : TransparencyMode := .reducible
  splitHypotheses : Bool := true
  splitNe : Bool := false
  preprocessors : List GlobalBranchingPreprocessor := defaultPreprocessors
  oracle : CertificateOracle := .simplexAlgorithmSparse
def LinarithConfig.updateReducibility (cfg : LinarithConfig) (reduce_default : Bool) :
    LinarithConfig :=
  if reduce_default then
    { cfg with transparency := .default, discharger := do evalTactic (← `(tactic| ring1!)) }
  else cfg
end
def getContrLemma (e : Expr) : MetaM (Name × Expr) := do
  match ← e.ineqOrNotIneq? with
  | (true, Ineq.lt, t, _) => pure (``lt_of_not_ge, t)
  | (true, Ineq.le, t, _) => pure (``le_of_not_gt, t)
  | (true, Ineq.eq, t, _) => pure (``eq_of_not_lt_of_not_gt, t)
  | (false, _, t, _) => pure (``Not.intro, t)
def applyContrLemma (g : MVarId) : MetaM (Option (Expr × Expr) × MVarId) := do
  try
    let (nm, tp) ← getContrLemma (← withReducible g.getType')
    let [g] ← g.apply (← mkConst' nm) | failure
    let (f, g) ← g.intro1P
    return (some (tp, .fvar f), g)
  catch _ => return (none, g)
abbrev ExprMultiMap α := Array (Expr × List α)
def ExprMultiMap.find {α : Type} (self : ExprMultiMap α) (k : Expr) : MetaM (Nat × List α) := do
  for h : i in [:self.size] do
    let (k', vs) := self[i]'h.2
    if ← isDefEq k' k then
      return (i, vs)
  return (self.size, [])
def ExprMultiMap.insert {α : Type} (self : ExprMultiMap α) (k : Expr) (v : α) :
    MetaM (ExprMultiMap α) := do
  for h : i in [:self.size] do
    if ← isDefEq (self[i]'h.2).1 k then
      return self.modify i fun (k, vs) => (k, v::vs)
  return self.push (k, [v])
def partitionByType (l : List Expr) : MetaM (ExprMultiMap Expr) :=
  l.foldlM (fun m h => do m.insert (← typeOfIneqProof h) h) #[]
def findLinarithContradiction (cfg : LinarithConfig) (g : MVarId) (ls : List (List Expr)) :
    MetaM Expr :=
  try
    ls.firstM (fun L => proveFalseByLinarith cfg.transparency cfg.oracle cfg.discharger g L)
  catch e => throwError "linarith failed to find a contradiction\n{g}\n{e.toMessageData}"
def runLinarith (cfg : LinarithConfig) (prefType : Option Expr) (g : MVarId)
    (hyps : List Expr) : MetaM Unit := do
  let singleProcess (g : MVarId) (hyps : List Expr) : MetaM Expr := g.withContext do
    linarithTraceProofs s!"after preprocessing, linarith has {hyps.length} facts:" hyps
    let hyp_set ← partitionByType hyps
    trace[linarith] "hypotheses appear in {hyp_set.size} different types"
      if let some t := prefType then
        let (i, vs) ← hyp_set.find t
        proveFalseByLinarith cfg.transparency cfg.oracle cfg.discharger g vs <|>
        findLinarithContradiction cfg g ((hyp_set.eraseIdxIfInBounds i).toList.map (·.2))
      else findLinarithContradiction cfg g (hyp_set.toList.map (·.2))
  let mut preprocessors := cfg.preprocessors
  if cfg.splitNe then
    preprocessors := Linarith.removeNe :: preprocessors
  if cfg.splitHypotheses then
    preprocessors := Linarith.splitConjunctions.globalize.branching :: preprocessors
  let branches ← preprocess preprocessors g hyps
  for (g, es) in branches do
    let r ← singleProcess g es
    g.assign r
  (Expr.mvar g).ensureHasNoMVars
partial def linarith (only_on : Bool) (hyps : List Expr) (cfg : LinarithConfig := {})
    (g : MVarId) : MetaM Unit := g.withContext do
  if (← whnfR (← instantiateMVars (← g.getType))).isEq then
    trace[linarith] "target is an equality: splitting"
    if let some [g₁, g₂] ← try? (g.apply (← mkConst' ``eq_of_not_lt_of_not_gt)) then
      linarith only_on hyps cfg g₁
      linarith only_on hyps cfg g₂
      return
  let (g, target_type, new_var) ← match ← applyContrLemma g with
  | (none, g) =>
    if cfg.exfalso then
      trace[linarith] "using exfalso"
      pure (← g.exfalso, none, none)
    else
      pure (g, none, none)
  | (some (t, v), g) => pure (g, some t, some v)
  g.withContext do
    let hyps ← (if only_on then return new_var.toList ++ hyps
      else return (← getLocalHyps).toList ++ hyps)
    linarithTraceProofs "linarith is running on the following hypotheses:" hyps
    runLinarith cfg target_type g hyps
end Linarith
open Parser Tactic Syntax
syntax linarithArgsRest := optConfig (&" only")? (" [" term,* "]")?
syntax (name := linarith) "linarith" "!"? linarithArgsRest : tactic
@[inherit_doc linarith] macro "linarith!" rest:linarithArgsRest : tactic =>
  `(tactic| linarith ! $rest:linarithArgsRest)
syntax (name := nlinarith) "nlinarith" "!"? linarithArgsRest : tactic
@[inherit_doc nlinarith] macro "nlinarith!" rest:linarithArgsRest : tactic =>
  `(tactic| nlinarith ! $rest:linarithArgsRest)
def elabLinarithArg (tactic : Name) (t : Term) : TacticM Expr := Term.withoutErrToSorry do
  let (e, mvars) ← elabTermWithHoles t none tactic
  unless mvars.isEmpty do
    throwErrorAt t "Argument passed to {tactic} has metavariables:{indentD e}"
  return e
declare_config_elab elabLinarithConfig Linarith.LinarithConfig
elab_rules : tactic
  | `(tactic| linarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) => withMainContext do
    let args ← ((args.map (TSepArray.getElems)).getD {}).mapM (elabLinarithArg `linarith)
    let cfg := (← elabLinarithConfig cfg).updateReducibility bang.isSome
    commitIfNoEx do liftMetaFinishingTactic <| Linarith.linarith o.isSome args.toList cfg
open Linarith
elab_rules : tactic
  | `(tactic| nlinarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) => withMainContext do
    let args ← ((args.map (TSepArray.getElems)).getD {}).mapM (elabLinarithArg `nlinarith)
    let cfg := (← elabLinarithConfig cfg).updateReducibility bang.isSome
    let cfg := { cfg with
      preprocessors := cfg.preprocessors.concat nlinarithExtras }
    commitIfNoEx do liftMetaFinishingTactic <| Linarith.linarith o.isSome args.toList cfg