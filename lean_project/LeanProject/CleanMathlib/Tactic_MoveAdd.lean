import Mathlib.Algebra.Group.Basic
import Mathlib.Lean.Meta
open Lean Expr
def Lean.Expr.getExprInputs : Expr → Array Expr
  | app fn arg        => #[fn, arg]
  | lam _ bt bb _     => #[bt, bb]
  | forallE _ bt bb _ => #[bt, bb]
  | letE _ t v b _    => #[t, v, b]
  | mdata _ e         => #[e]
  | proj _ _ e        => #[e]
  | _ => #[]
partial
def Lean.Expr.size (e : Expr) : ℕ := (e.getExprInputs.map size).foldl (· + ·) 1
namespace Mathlib.MoveAdd
section ExprProcessing
section reorder
variable {α : Type*} [BEq α]
def uniquify : List α → List (α × ℕ)
  | []    => []
  | m::ms =>
    let lms := uniquify ms
    (m, 0) :: (lms.map fun (x, n) => if x == m then (x, n + 1) else (x, n))
def weight (L : List (α × Bool)) (a : α) : ℤ :=
  let l := L.length
  match L.find? (Prod.fst · == a) with
    | some (_, b) => if b then - l + (L.indexOf (a, b) : ℤ) else (L.indexOf (a, b) + 1 : ℤ)
    | none => 0
def reorderUsing (toReorder : List α) (instructions : List (α × Bool)) : List α :=
  let uInstructions :=
    let (as, as?) := instructions.unzip
    (uniquify as).zip as?
  let uToReorder := (uniquify toReorder).toArray
  let reorder := uToReorder.qsort fun x y =>
    match uInstructions.find? (Prod.fst · == x), uInstructions.find? (Prod.fst · == y) with
      | none, none =>
        ((uToReorder.indexOf? x).map Fin.val).get! ≤ ((uToReorder.indexOf? y).map Fin.val).get!
      | _, _ => weight uInstructions x ≤ weight uInstructions y
  (reorder.map Prod.fst).toList
end reorder
def prepareOp (sum : Expr) : Expr :=
  let opargs := sum.getAppArgs
  (opargs.toList.take (opargs.size - 2)).foldl (fun x y => Expr.app x y) sum.getAppFn
partial
def sumList (prepOp : Expr) (left_assoc? : Bool) : List Expr → Expr
  | []    => default
  | [a]   => a
  | a::as =>
    if left_assoc? then
      Expr.app (prepOp.app a) (sumList prepOp true as)
    else
      as.foldl (fun x y => Expr.app (prepOp.app x) y) a
end ExprProcessing
open Meta
variable (op : Name)
variable (R : Expr) in
partial def getAddends (sum : Expr) : MetaM (Array Expr) := do
  if sum.isAppOf op then
    let inR ← sum.getAppArgs.filterM fun r => do isDefEq R (← inferType r <|> pure R)
    let new ← inR.mapM (getAddends ·)
    return new.foldl Array.append  #[]
  else return #[sum]
partial def getOps (sum : Expr) : MetaM (Array ((Array Expr) × Expr)) := do
  let summands ← getAddends op (← inferType sum <|> return sum) sum
  let (first, rest) := if summands.size == 1 then (#[], sum.getExprInputs) else
    (#[(summands, sum)], summands)
  let rest ← rest.mapM getOps
  return rest.foldl Array.append first
def rankSums (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM (List (Expr × Expr)) := do
  let sums ← getOps op (← instantiateMVars tgt)
  let candidates := sums.map fun (addends, sum) => do
    let reord := reorderUsing addends.toList instructions
    let left_assoc? := sum.getAppFn.isConstOf `And || sum.getAppFn.isConstOf `Or
    let resummed := sumList (prepareOp sum) left_assoc? reord
    if (resummed != sum) then some (sum, resummed) else none
  return (candidates.toList.reduceOption.toArray.qsort
    (fun x y : Expr × Expr ↦ (y.1.size  ≤ x.1.size))).toList
def permuteExpr (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM Expr := do
  let permInstructions ← rankSums op tgt instructions
  if permInstructions == [] then throwError "The goal is already in the required form"
  let mut permTgt := tgt
  for (old, new) in permInstructions do
    permTgt := permTgt.replace (if · == old then new else none)
  return permTgt
```
-/
def pairUp : List (Expr × Bool × Syntax) → List Expr →
    MetaM ((List (Expr × Bool)) × List (Expr × Bool × Syntax))
  | (m::ms), l => do
    match ← l.findM? (isDefEq · m.1) with
      | none => let (found, unfound) ← pairUp ms l; return (found, m::unfound)
      | some d => let (found, unfound) ← pairUp ms (l.erase d)
                  return ((d, m.2.1)::found, unfound)
  | _, _ => return ([], [])
def move_oper_simpCtx : MetaM Simp.Context := do
  let simpNames := Elab.Tactic.simpOnlyBuiltins ++ [
    ``add_comm, ``add_assoc, ``add_left_comm,  
    ``mul_comm, ``mul_assoc, ``mul_left_comm,  
    ``and_comm, ``and_assoc, ``and_left_comm,  
    ``or_comm,  ``or_assoc,  ``or_left_comm,   
    ``max_comm, ``max_assoc, ``max_left_comm,  
    ``min_comm, ``min_assoc, ``min_left_comm   
    ]
  let simpThms ← simpNames.foldlM (·.addConst ·) ({} : SimpTheorems)
  Simp.mkContext {} (simpTheorems := #[simpThms])
def reorderAndSimp (mv : MVarId) (instr : List (Expr × Bool)) :
    MetaM (List MVarId) := mv.withContext do
  let permExpr ← permuteExpr op (← mv.getType'') instr
  let eqmpr ← mkAppM ``Eq.mpr #[← mkFreshExprMVar (← mkEq (← mv.getType) permExpr)]
  let twoGoals ← mv.apply eqmpr
  guard (twoGoals.length == 2) <|>
    throwError m!"There should only be 2 goals, instead of {twoGoals.length}"
  let permGoal ← twoGoals.filterM fun v => return !(← v.isAssigned)
  match ← (simpGoal (permGoal[1]!) (← move_oper_simpCtx)) with
    | (some x, _) => throwError m!"'move_oper' could not solve {indentD x.2}"
    | (none, _) => return permGoal
def unifyMovements (data : Array (Expr × Bool × Syntax)) (tgt : Expr) :
    MetaM (List (Expr × Bool) × (List MessageData × List Syntax) × Array MessageData) := do
  let ops ← getOps op tgt
  let atoms := (ops.map Prod.fst).flatten.toList.filter (!isBVar ·)
  let (instr, neverMatched) ← pairUp data.toList atoms
  let dbgMsg := #[m!"Matching of input variables:\n\
    * pre-match:  {data.map (Prod.snd ∘ Prod.snd)}\n\
    * post-match: {instr}",
    m!"\nMaximum number of iterations: {ops.size}"]
  let errMsg := neverMatched.map fun (t, a, stx) => (if a then m!"← {t}" else m!"{t}", stx)
  return (instr, errMsg.unzip, dbgMsg)
section parsing
open Elab Parser Tactic
def parseArrows : TSyntax `Lean.Parser.Tactic.rwRuleSeq → TermElabM (Array (Expr × Bool × Syntax))
  | `(rwRuleSeq| [$rs,*]) => do
    rs.getElems.mapM fun rstx => do
      let r : Syntax := rstx
      return (← Term.elabTerm r[1]! none, ! r[0]!.isNone, rstx)
  | _ => failure
initialize registerTraceClass `Tactic.move_oper
elab (name := moveOperTac) "move_oper" id:ident rws:rwRuleSeq : tactic => withMainContext do
  let op := id.getId
  let (instr, (unmatched, stxs), dbgMsg) ← unifyMovements op (← parseArrows rws)
                                                              (← instantiateMVars (← getMainTarget))
  unless unmatched.length = 0 do
    let _ ← stxs.mapM (logErrorAt · "") 
    trace[Tactic.move_oper] dbgMsg.foldl (fun x y => (x.compose y).compose "\n\n
    throwErrorAt stxs[0]! m!"Errors:\nThe terms in '{unmatched}' were not matched to any atom"
  replaceMainGoal (← reorderAndSimp op (← getMainGoal) instr)
@[inherit_doc moveOperTac]
elab "move_add" rws:rwRuleSeq : tactic => do
  let hadd := mkIdent ``HAdd.hAdd
  evalTactic (← `(tactic| move_oper $hadd $rws))
@[inherit_doc moveOperTac]
elab "move_mul" rws:rwRuleSeq : tactic => do
  let hmul := mkIdent ``HMul.hMul
  evalTactic (← `(tactic| move_oper $hmul $rws))
end parsing
end MoveAdd
end Mathlib