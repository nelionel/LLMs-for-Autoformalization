import Mathlib.Tactic.Linarith.Datatypes
import Mathlib.Tactic.Zify
import Mathlib.Tactic.CancelDenoms.Core
import Batteries.Data.RBMap.Basic
import Mathlib.Control.Basic
import Mathlib.Util.AtomM
namespace Linarith
open Lean
open Elab Tactic Meta
open Qq
open Mathlib
open Mathlib.Tactic (AtomM)
open Batteries (RBSet)
partial def splitConjunctions : Preprocessor where
  name := "split conjunctions"
  transform := aux
where
  aux (proof : Expr) : MetaM (List Expr) := do
    match (← instantiateMVars (← inferType proof)).getAppFnArgs with
    | (``And, #[_, _]) =>
      pure ((← aux (← mkAppM ``And.left #[proof])) ++
        (← aux (← mkAppM ``And.right #[proof])))
    | _ => pure [proof]
partial def filterComparisons : Preprocessor where
  name := "filter terms that are not proofs of comparisons"
  transform h := do
    let tp ← instantiateMVars (← inferType h)
    try
      let (b, rel, _) ← tp.ineqOrNotIneq?
      if b || rel != Ineq.eq then pure [h] else pure []
    catch _ => pure []
section removeNegations
def flipNegatedComparison (prf : Expr) (e : Expr) : MetaM (Option Expr) :=
  match e.getAppFnArgs with
  | (``LE.le, #[_, _, _, _]) => try? <| mkAppM ``lt_of_not_ge #[prf]
  | (``LT.lt, #[_, _, _, _]) => try? <| mkAppM ``le_of_not_gt #[prf]
  | _ => throwError "Not a comparison (flipNegatedComparison): {e}"
def removeNegations : Preprocessor where
  name := "replace negations of comparisons"
  transform h := do
    let t : Q(Prop) ← whnfR (← inferType h)
    match t with
    | ~q(¬ $p) =>
      match ← flipNegatedComparison h (← whnfR p) with
      | some h' =>
        trace[linarith] "removing negation in {h}"
        return [h']
      | _ => return [h]
    | _ => return [h]
end removeNegations
section natToInt
open Mathlib.Tactic.Zify
partial def isNatProp (e : Expr) : MetaM Bool := succeeds <| do
  let (_, _, .const ``Nat [], _, _) ← e.ineqOrNotIneq? | failure
def isNatCoe (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[target, _, n]) => some ⟨n, target⟩
  | _ => none
partial def getNatComparisons (e : Expr) : List (Expr × Expr) :=
  match isNatCoe e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``Neg.neg, #[_, _, a]) => getNatComparisons a
    | _ => []
def mk_natCast_nonneg_prf (p : Expr × Expr) : MetaM (Option Expr) :=
  match p with
  | ⟨e, target⟩ => try commitIfNoEx (mkAppM ``natCast_nonneg #[target, e])
    catch e => do
      trace[linarith] "Got exception when using cast {e.toMessageData}"
      return none
def Expr.Ord : Ord Expr :=
⟨fun a b => if Expr.lt a b then .lt else if a.equal b then .eq else .gt⟩
attribute [local instance] Expr.Ord
def natToInt : GlobalBranchingPreprocessor where
  name := "move nats to ints"
  transform g l := do
    let l ← l.mapM fun h => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      if ← isNatProp t then
        let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (zifyProof none h t))
          | throwError "zifyProof failed on {h}"
        if ← succeeds t'.ineqOrNotIneq? then
          pure h'
        else
          pure h
      else
        pure h
    let nonnegs ← l.foldlM (init := ∅) fun (es : RBSet (Expr × Expr) lexOrd.compare) h => do
      try
        let (_, _, a, b) ← (← inferType h).ineq?
        pure <| (es.insertMany (getNatComparisons a)).insertMany (getNatComparisons b)
      catch _ => pure es
    pure [(g, ((← nonnegs.toList.filterMapM mk_natCast_nonneg_prf) ++ l : List Expr))]
end natToInt
section strengthenStrictInt
def mkNonstrictIntProof (pf : Expr) : MetaM (Option Expr) := do
  match ← (← inferType pf).ineqOrNotIneq? with
  | (true, Ineq.lt, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]]) pf
  | (false, Ineq.le, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[b, a]])
      (← mkAppM ``lt_of_not_ge #[pf])
  | _ => return none
def strengthenStrictInt : Preprocessor where
  name := "strengthen strict inequalities over int"
  transform h := return [(← mkNonstrictIntProof h).getD h]
end strengthenStrictInt
section compWithZero
partial def rearrangeComparison (e : Expr) : MetaM (Option Expr) := do
  match ← (← inferType e).ineq? with
  | (Ineq.le, _) => try? <| mkAppM ``Linarith.sub_nonpos_of_le #[e]
  | (Ineq.lt, _) => try? <| mkAppM ``Linarith.sub_neg_of_lt #[e]
  | (Ineq.eq, _) => try? <| mkAppM ``sub_eq_zero_of_eq #[e]
def compWithZero : Preprocessor where
  name := "make comparisons with zero"
  transform e := return (← rearrangeComparison e).toList
end compWithZero
section cancelDenoms
theorem without_one_mul {M : Type*} [MulOneClass M] {a b : M} (h : 1 * a = b) : a = b := by
  rwa [one_mul] at h
def normalizeDenominatorsLHS (h lhs : Expr) : MetaM Expr := do
  let mut (v, lhs') ← CancelDenoms.derive lhs
  if v = 1 then
    lhs' ← mkAppM ``without_one_mul #[lhs']
  let (_, h'') ← mkSingleCompZeroOf v h
  try
    h''.rewriteType lhs'
  catch e =>
    dbg_trace
      s!"Error in Linarith.normalizeDenominatorsLHS: {← e.toMessageData.toString}"
    throw e
def cancelDenoms : Preprocessor where
  name := "cancel denominators"
  transform := fun pf => (do
      let (_, lhs) ← parseCompAndExpr (← inferType pf)
      guard <| lhs.containsConst <| fun n =>
        n = ``HDiv.hDiv || n = ``Div.div || n = ``Inv.inv || n == ``OfScientific.ofScientific
      pure [← normalizeDenominatorsLHS pf lhs])
    <|> return [pf]
end cancelDenoms
section nlinarith
partial def findSquares (s : RBSet (Nat × Bool) lexOrd.compare) (e : Expr) :
    AtomM (RBSet (Nat × Bool) lexOrd.compare) :=
  if e.hasLooseBVars then return s else
  match e.getAppFnArgs with
  | (``HPow.hPow, #[_, _, _, _, a, b]) => match b.numeral? with
    | some 2 => do
      let s ← findSquares s a
      let (ai, _) ← AtomM.addAtom a
      return (s.insert (ai, true))
    | _ => e.foldlM findSquares s
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
    let (ai, _) ← AtomM.addAtom a
    let (bi, _) ← AtomM.addAtom b
    if ai = bi then do
      let s ← findSquares s a
      return (s.insert (ai, false))
    else
      e.foldlM findSquares s
  | _ => e.foldlM findSquares s
def nlinarithExtras : GlobalPreprocessor where
  name := "nonlinear arithmetic extras"
  transform ls := do
    let s ← AtomM.run .reducible do
      let si ← ls.foldrM (fun h s' => do findSquares s' (← instantiateMVars (← inferType h)))
        RBSet.empty
      si.toList.mapM fun (i, is_sq) => return ((← get).atoms[i]!, is_sq)
    let new_es ← s.filterMapM fun (e, is_sq) =>
      observing? <| mkAppM (if is_sq then ``sq_nonneg else ``mul_self_nonneg) #[e]
    let new_es ← compWithZero.globalize.transform new_es
    trace[linarith] "nlinarith preprocessing found squares"
    trace[linarith] "{s}"
    linarithTraceProofs "so we added proofs" new_es
    let with_comps ← (new_es ++ ls).mapM (fun e => do
      let tp ← inferType e
      try
        let ⟨ine, _⟩ ← parseCompAndExpr tp
        pure (ine, e)
      catch _ => pure (Ineq.lt, e))
    let products ← with_comps.mapDiagM fun (⟨posa, a⟩ : Ineq × Expr) ⟨posb, b⟩ =>
      try
        (some <$> match posa, posb with
          | Ineq.eq, _ => mkAppM ``zero_mul_eq #[a, b]
          | _, Ineq.eq => mkAppM ``mul_zero_eq #[a, b]
          | Ineq.lt, Ineq.lt => mkAppM ``mul_pos_of_neg_of_neg #[a, b]
          | Ineq.lt, Ineq.le => do
              let a ← mkAppM ``le_of_lt #[a]
              mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
          | Ineq.le, Ineq.lt => do
              let b ← mkAppM ``le_of_lt #[b]
              mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
          | Ineq.le, Ineq.le => mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b])
      catch _ => pure none
    let products ← compWithZero.globalize.transform products.reduceOption
    return (new_es ++ ls ++ products)
end nlinarith
section removeNe
partial def removeNe_aux : MVarId → List Expr → MetaM (List Branch) := fun g hs => do
  let some (e, α, a, b) ← hs.findSomeM? (fun e : Expr => do
    let some (α, a, b) := (← instantiateMVars (← inferType e)).ne?' | return none
    return some (e, α, a, b)) | return [(g, hs)]
  let [ng1, ng2] ← g.apply (← mkAppOptM ``Or.elim #[none, none, ← g.getType,
      ← mkAppOptM ``lt_or_gt_of_ne #[α, none, a, b, e]]) | failure
  let do_goal : MVarId → MetaM (List Branch) := fun g => do
    let (f, h) ← g.intro1
    h.withContext do
      let ls ← removeNe_aux h <| hs.removeAll [e]
      return ls.map (fun b : Branch => (b.1, (.fvar f)::b.2))
  return ((← do_goal ng1) ++ (← do_goal ng2))
def removeNe : GlobalBranchingPreprocessor where
  name := "removeNe"
  transform := removeNe_aux
end removeNe
def defaultPreprocessors : List GlobalBranchingPreprocessor :=
  [filterComparisons, removeNegations, natToInt, strengthenStrictInt,
    compWithZero, cancelDenoms]
def preprocess (pps : List GlobalBranchingPreprocessor) (g : MVarId) (l : List Expr) :
    MetaM (List Branch) := g.withContext <|
  pps.foldlM (fun ls pp => return (← ls.mapM fun (g, l) => do pp.process g l).flatten) [(g, l)]
end Linarith