import Lean.Meta.Tactic.Rewrites
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.EditDistance.Estimator
import Mathlib.Data.MLList.BestFirst
import Mathlib.Order.Interval.Finset.Nat
import Batteries.Data.MLList.Heartbeats
namespace Mathlib.Tactic.RewriteSearch
open Lean Meta
open Lean.Meta.Rewrites
open Lean.Meta.LazyDiscrTree (ModuleDiscrTreeRef)
initialize registerTraceClass `rw_search
initialize registerTraceClass `rw_search.detail
partial def splitDelimiters (s : String) : List String :=
  let rec  auxStart front pre :=
    let head := s.get front
    if head = '(' || head = '[' then
      auxStart (s.next front) (head.toString :: pre)
    else
      (front, pre)
  let rec  auxEnd back suff :=
    let last := s.get back
    if last = ')' || last = ']' || last = ',' then
      auxEnd (s.prev back) (last.toString :: suff)
    else
      (back, suff)
  let (frontAfterStart, pre) := auxStart 0 []
  let (backAfterEnd, suff) := auxEnd (s.prev s.endPos) []
  pre.reverse ++ [s.extract frontAfterStart (s.next backAfterEnd)] ++ suff
def tokenize (e : Expr) : MetaM (List String) := do
  let s := (← ppExpr e).pretty
  return s.splitOn.map splitDelimiters |>.flatten
structure SearchNode where mk' ::
  history : Array (Nat × Expr × Bool)
  mctx : MetavarContext
  goal : MVarId
  type : Expr
  ppGoal : String
  lhs : List String
  rhs : List String
  rfl? : Option Bool := none
  dist? : Option Nat := none
namespace SearchNode
def editCost : Levenshtein.Cost String String Nat := Levenshtein.defaultCost
def compute_rfl? (n : SearchNode) : MetaM SearchNode := do
  try
    withoutModifyingState <| withMCtx n.mctx do
      n.goal.refl
      pure { n with mctx := ← getMCtx, rfl? := some true }
  catch _e =>
    withMCtx n.mctx do
      if (←  try? n.goal.applyRfl).isSome then
        pure { n with mctx := ← getMCtx, rfl? := some true }
      else
        pure { n with rfl? := some false }
def compute_dist? (n : SearchNode) : SearchNode :=
  match n.dist? with
  | some _ => n
  | none =>
    { n with dist? := some (levenshtein editCost n.lhs n.rhs) }
def toString (n : SearchNode) : MetaM String := do
  let n := n.compute_dist?
  let tac ← match n.history.back? with
  | some (_, e, true) => do let pp ← ppExpr e; pure s!"rw [← {pp}]"
  | some (_, e, false) => do let pp ← ppExpr e; pure s!"rw [{pp}]"
  | none => pure ""
  return s!"depth: {n.history.size}\n\
    history: {n.history.map fun p => hash p % 10000}\n\
    {tac}\n\
    distance: {n.dist?.get!}+{n.history.size}, {n.ppGoal.length}"
def mk (history : Array (Nat × Expr × Bool)) (goal : MVarId) (ctx : Option MetavarContext := none) :
    MetaM (Option SearchNode) := goal.withContext do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  match type.eq? with
  | none => return none
  | some (_, lhs, rhs) =>
    let lhsTokens ← tokenize lhs
    let rhsTokens ← tokenize rhs
    let r :=
      { history := history
        mctx := ← ctx.getDM getMCtx
        goal := goal
        type := type
        ppGoal := (← ppExpr type).pretty
        lhs := lhsTokens
        rhs := rhsTokens }
    return some r
def init (goal : MVarId) : MetaM (Option SearchNode) := mk #[] goal
def push (n : SearchNode) (expr : Expr) (symm : Bool) (k : Nat) (g : MVarId)
    (ctx : Option MetavarContext := none) : MetaM (Option SearchNode) :=
  mk (n.history.push (k, expr, symm)) g ctx
def lastIdx (n : SearchNode) : Nat :=
  match n.history.back? with
  | some (k, _) => k
  | none => 0
instance : Ord SearchNode where
  compare := compareOn fun n => toLex (toLex (n.ppGoal.length, n.lastIdx), n.ppGoal)
def penalty (n : SearchNode) : Nat := n.lastIdx.log2 + n.ppGoal.length.log2
abbrev prio (n : SearchNode) : Thunk Nat :=
  (Thunk.pure n.penalty) + (Thunk.mk fun _ => levenshtein editCost n.lhs n.rhs)
abbrev estimator (n : SearchNode) : Type :=
  Estimator.trivial n.penalty × LevenshteinEstimator editCost n.lhs n.rhs
def rewrite (n : SearchNode) (r : Rewrites.RewriteResult) (k : Nat) :
    MetaM (Option SearchNode) :=
  withMCtx r.mctx do
    let goal' ← n.goal.replaceTargetEq r.result.eNew r.result.eqProof
    n.push r.expr r.symm k goal' (← getMCtx)
def rewrites (hyps : Array (Expr × Bool × Nat))
    (lemmas : ModuleDiscrTreeRef (Name × RwDirection))
    (forbidden : NameSet := ∅) (n : SearchNode) : MLList MetaM SearchNode := .squash fun _ => do
  if ← isTracingEnabledFor `rw_search then do
    trace[rw_search] "searching:\n{← toString n}"
  let candidates ← rewriteCandidates hyps lemmas n.type forbidden
  return MLList.ofArray candidates
    |>.filterMapM (fun ⟨lem, symm, weight⟩ =>
        rwLemma n.mctx n.goal n.type .solveByElim lem symm weight)
    |>.enum
    |>.filterMapM fun ⟨k, r⟩ => do n.rewrite r k
def search (n : SearchNode)
    (stopAtRfl := true) (stopAtDistZero := true)
    (forbidden : NameSet := ∅) (maxQueued : Option Nat := none) :
    MLList MetaM SearchNode := .squash fun _ => do
  let hyps ← localHypotheses
  let moduleRef ← createModuleTreeRef
  let search := bestFirstSearchCore (maxQueued := maxQueued)
    (β := String) (removeDuplicatesBy? := some SearchNode.ppGoal)
    prio estimator (rewrites hyps moduleRef forbidden) n
  let search ←
    if ← isTracingEnabledFor `rw_search then do
      pure <| search.mapM fun n => do trace[rw_search] "{← toString n}"; pure n
    else
      pure search
  let search := if stopAtRfl then
    search.mapM compute_rfl? |>.takeUpToFirst fun n => n.rfl? = some true
  else
    search
  return if stopAtDistZero then
    search.map (fun r => r.compute_dist?) |>.takeUpToFirst (fun r => r.dist? = some 0)
  else
    search
end SearchNode
open Elab Tactic Lean.Parser.Tactic
syntax "rw_search" (rewrites_forbidden)? : tactic
open Lean.Meta.Tactic.TryThis
elab_rules : tactic |
    `(tactic| rw_search%$tk $[[ $[-$forbidden],* ]]?) => withMainContext do
  let forbidden : NameSet :=
    ((forbidden.getD #[]).map Syntax.getId).foldl (init := ∅) fun s n => s.insert n
  let .some init ← SearchNode.init (← getMainGoal) | throwError "Goal is not an equality."
  let results := init.search (forbidden := forbidden) |>.whileAtLeastHeartbeatsPercent 20
  let results ← results.force
  let min ← match results with
  | [] => failure
  | h :: t =>
      pure <| t.foldl (init := h) fun r₁ r₂ =>
        if r₁.rfl? = some true then r₁
        else if r₂.rfl? = some true then r₂
        else if r₁.dist?.getD 0 ≤ r₂.dist?.getD 0 then r₁ else r₂
  setMCtx min.mctx
  replaceMainGoal [min.goal]
  let type? ← if min.rfl? = some true then pure none else do pure <| some (← min.goal.getType)
  addRewriteSuggestion tk (min.history.toList.map (·.2))
    type? (origSpan? := ← getRef)
end RewriteSearch
end Mathlib.Tactic