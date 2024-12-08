import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Control.Basic
namespace Mathlib.Tactic
open Lean Meta Elab Tactic Term Qq Int
namespace IntervalCases
structure IntervalCasesSubgoal where
  rhs : Expr
  value : Int
  goal : MVarId
inductive Bound
  | lt (n : ℤ)
  | le (n : ℤ)
def Bound.asLower : Bound → ℤ
  | .lt n => n + 1
  | .le n => n
def Bound.asUpper : Bound → ℤ
  | .lt n => n - 1
  | .le n => n
def parseBound (ty : Expr) : MetaM (Expr × Expr × Bool × Bool) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Not 1 then
    let ty ← whnfR ty.appArg!
    if ty.isAppOfArity ``LT.lt 4 then
      pure (ty.appArg!, ty.appFn!.appArg!, false, false)
    else if ty.isAppOfArity ``LE.le 4 then
      pure (ty.appArg!, ty.appFn!.appArg!, true, false)
    else failure
  else if ty.isAppOfArity ``LT.lt 4 then
    pure (ty.appFn!.appArg!, ty.appArg!, true, true)
  else if ty.isAppOfArity ``LE.le 4 then
    pure (ty.appFn!.appArg!, ty.appArg!, false, true)
  else failure
structure Methods where
  initLB (e : Expr) : MetaM (Bound × Expr × Expr) := failure
  initUB (e : Expr) : MetaM (Bound × Expr × Expr) := failure
  proveLE : Expr → Expr → MetaM Expr
  proveLT : Expr → Expr → MetaM Expr
  roundUp : Expr → Expr → Expr → Expr → MetaM Expr
  roundDown : Expr → Expr → Expr → Expr → MetaM Expr
  eval : Expr → MetaM (Int × Expr × Expr)
  mkNumeral : Int → MetaM Expr
variable {α : Type*} {a b a' b' : α}
theorem of_not_lt_left [LinearOrder α] (h : ¬(a:α) < b) (eq : a = a') : b ≤ a' := eq ▸ not_lt.1 h
theorem of_not_lt_right [LinearOrder α] (h : ¬(a:α) < b) (eq : b = b') : b' ≤ a := eq ▸ not_lt.1 h
theorem of_not_le_left [LE α] (h : ¬(a:α) ≤ b) (eq : a = a') : ¬a' ≤ b := eq ▸ h
theorem of_not_le_right [LE α] (h : ¬(a:α) ≤ b) (eq : b = b') : ¬a ≤ b' := eq ▸ h
theorem of_lt_left [LinearOrder α] (h : (a:α) < b) (eq : a = a') : ¬b ≤ a' := eq ▸ not_le.2 h
theorem of_lt_right [LinearOrder α] (h : (a:α) < b) (eq : b = b') : ¬b' ≤ a := eq ▸ not_le.2 h
theorem of_le_left [LE α] (h : (a:α) ≤ b) (eq : a = a') : a' ≤ b := eq ▸ h
theorem of_le_right [LE α] (h : (a:α) ≤ b) (eq : b = b') : a ≤ b' := eq ▸ h
def Methods.getBound (m : Methods) (e : Expr) (pf : Expr) (lb : Bool) :
    MetaM (Bound × Expr × Expr) := do
  let (e', c) ← match ← parseBound (← inferType pf), lb with
    | (b, a, false, false), false =>
      let (z, a', eq) ← m.eval a; pure (b, .le z, a', ← mkAppM ``of_not_lt_left #[pf, eq])
    | (b, a, false, false), true =>
      let (z, b', eq) ← m.eval b; pure (a, .le z, b', ← mkAppM ``of_not_lt_right #[pf, eq])
    | (a, b, false, true), false =>
      let (z, b', eq) ← m.eval b; pure (a, .le z, b', ← mkAppM ``of_le_right #[pf, eq])
    | (a, b, false, true), true =>
      let (z, a', eq) ← m.eval a; pure (b, .le z, a', ← mkAppM ``of_le_left #[pf, eq])
    | (b, a, true, false), false =>
      let (z, a', eq) ← m.eval a; pure (b, .lt z, a', ← mkAppM ``of_not_le_left #[pf, eq])
    | (b, a, true, false), true =>
      let (z, b', eq) ← m.eval b; pure (a, .lt z, b', ← mkAppM ``of_not_le_right #[pf, eq])
    | (a, b, true, true), false =>
      let (z, b', eq) ← m.eval b; pure (a, .lt z, b', ← mkAppM ``of_lt_right #[pf, eq])
    | (a, b, true, true), true =>
      let (z, a', eq) ← m.eval a; pure (b, .lt z, a', ← mkAppM ``of_lt_left #[pf, eq])
  let .true ← withNewMCtxDepth <| withReducible <| isDefEq e e' | failure
  pure c
theorem le_of_not_le_of_le {hi n lo : α} [LinearOrder α] (h1 : ¬hi ≤ n) (h2 : hi ≤ lo) :
    (n:α) ≤ lo :=
  le_trans (le_of_not_le h1) h2
def Methods.inconsistentBounds (m : Methods)
    (z1 z2 : Bound) (e1 e2 p1 p2 e : Expr) : MetaM Expr := do
  match z1, z2 with
  | .le lo, .lt hi =>
    if lo == hi then return p2.app p1
    return p2.app (← mkAppM ``le_trans #[← m.proveLE e2 e1, p1])
  | .lt lo, .le hi =>
    if lo == hi then return p1.app p2
    return p1.app (← mkAppM ``le_trans #[p2, ← m.proveLE e2 e1])
  | .le _, .le _ => return (← m.proveLT e2 e1).app (← mkAppM ``le_trans #[p1, p2])
  | .lt lo, .lt hi =>
    if hi ≤ lo then return p1.app (← mkAppM ``le_of_not_le_of_le #[p2, ← m.proveLE e2 e1])
    let e3 ← m.mkNumeral (hi - 1)
    let p3 ← m.roundDown e e2 e3 p2
    return p1.app (← mkAppM ``le_trans #[p3, ← m.proveLE e3 e1])
partial def Methods.bisect (m : Methods) (g : MVarId) (cases : Subarray IntervalCasesSubgoal)
    (z1 z2 : Bound) (e1 e2 p1 p2 e : Expr) : MetaM Unit := g.withContext do
  if 1 < cases.size then
    let tgt ← g.getType
    let mid := cases.size / 2
    let z3 := z1.asLower + mid
    let e3 ← m.mkNumeral z3
    let le ← mkAppM ``LE.le #[e3, e]
    let g₁ ← mkFreshExprMVar (← mkArrow (mkNot le) tgt) .syntheticOpaque
    let g₂ ← mkFreshExprMVar (← mkArrow le tgt) .syntheticOpaque
    g.assign <| ← mkAppM ``dite #[le, g₂, g₁]
    let (x₁, g₁) ← g₁.mvarId!.intro1
    m.bisect g₁ cases[:mid] z1 (.lt z3) e1 e3 p1 (.fvar x₁) e
    let (x₂, g₂) ← g₂.mvarId!.intro1
    m.bisect g₂ cases[mid:] (.le z3) z2 e3 e2 (.fvar x₂) p2 e
  else if _x : 0 < cases.size then
    let { goal, rhs, .. } := cases[0]
    let pf₁ ← match z1 with | .le _ => pure p1 | .lt _ => m.roundUp e1 e rhs p1
    let pf₂ ← match z2 with | .le _ => pure p2 | .lt _ => m.roundDown e e2 rhs p2
    g.assign (.app (.mvar goal) (← mkAppM ``le_antisymm #[pf₂, pf₁]))
  else panic! "no goals"
def natMethods : Methods where
  initLB (e : Q(ℕ)) :=
    pure (.le 0, q(0), q(Nat.zero_le $e))
  eval e := do
    let ⟨z, e, p⟩ := (← NormNum.derive (α := (q(ℕ) : Q(Type))) e).toRawIntEq.get!
    pure (z, e, p)
  proveLE (lhs rhs : Q(ℕ)) := mkDecideProof q($lhs ≤ $rhs)
  proveLT (lhs rhs : Q(ℕ)) := mkDecideProof q(¬$rhs ≤ $lhs)
  roundUp (lhs rhs _ : Q(ℕ)) (p : Q(¬$rhs ≤ $lhs)) := pure q(Nat.gt_of_not_le $p)
  roundDown (lhs _ rhs' : Q(ℕ)) (p : Q(¬Nat.succ $rhs' ≤ $lhs)) := pure q(Nat.ge_of_not_lt $p)
  mkNumeral
    | (i : ℕ) => pure q($i)
    | _ => failure
theorem _root_.Int.add_one_le_of_not_le {a b : ℤ} (h : ¬b ≤ a) : a + 1 ≤ b :=
  Int.add_one_le_iff.2 (Int.not_le.1 h)
theorem _root_.Int.le_sub_one_of_not_le {a b : ℤ} (h : ¬b ≤ a) : a ≤ b - 1 :=
  Int.le_sub_one_iff.2 (Int.not_le.1 h)
def intMethods : Methods where
  eval e := do
    let ⟨z, e, p⟩ := (← NormNum.derive (α := (q(ℤ) : Q(Type))) e).toRawIntEq.get!
    pure (z, e, p)
  proveLE (lhs rhs : Q(ℤ)) := mkDecideProof q($lhs ≤ $rhs)
  proveLT (lhs rhs : Q(ℤ)) := mkDecideProof q(¬$rhs ≤ $lhs)
  roundUp (lhs rhs _ : Q(ℤ)) (p : Q(¬$rhs ≤ $lhs)) := pure q(Int.add_one_le_of_not_le $p)
  roundDown (lhs rhs _ : Q(ℤ)) (p : Q(¬$rhs ≤ $lhs)) := pure q(Int.le_sub_one_of_not_le $p)
  mkNumeral
    | (i : Nat) => let n : Q(ℕ) := mkRawNatLit i; pure q(OfNat.ofNat $n : ℤ)
    | .negSucc i => let n : Q(ℕ) := mkRawNatLit (i+1); pure q(-OfNat.ofNat $n : ℤ)
def intervalCases (g : MVarId) (e e' : Expr) (lbs ubs : Array Expr) (mustUseBounds := false) :
    MetaM (Array IntervalCasesSubgoal) := g.withContext do
  let α ← whnfR (← inferType e)
  let m ←
    if α.isConstOf ``Nat then pure natMethods else
    if α.isConstOf ``Int then pure intMethods else
    throwError "interval_cases failed: unsupported type {α}"
  let mut lb ← try? (m.initLB e)
  for pf in lbs do
    if let some lb1 ← try? (m.getBound e pf true) then
      if lb.all (·.1.asLower < lb1.1.asLower) then
        lb := some lb1
    else if mustUseBounds then
      throwError "interval_cases failed: provided bound '{← inferType pf}' cannot be evaluated"
  let mut ub ← try? (m.initUB e)
  for pf in ubs do
    if let some ub1 ← try? (m.getBound e pf false) then
      if ub.all (·.1.asUpper > ub1.1.asUpper) then
        ub := some ub1
    else if mustUseBounds then
      throwError "interval_cases failed: provided bound '{← inferType pf}' cannot be evaluated"
  match lb, ub with
  | some (z1, e1, p1), some (z2, e2, p2) =>
    if z1.asLower > z2.asUpper then
      (← g.exfalso).assign (← m.inconsistentBounds z1 z2 e1 e2 p1 p2 e)
      pure #[]
    else
      let mut goals := #[]
      let lo := z1.asLower
      let tgt ← g.getType
      let tag ← g.getTag
      for i in [:(z2.asUpper-lo+1).toNat] do
        let z := lo+i
        let rhs ← m.mkNumeral z
        let ty ← mkArrow (← mkEq e rhs) tgt
        let goal ← mkFreshExprMVar ty .syntheticOpaque (appendTag tag (.mkSimple (toString z)))
        goals := goals.push { rhs, value := z, goal := goal.mvarId! }
      m.bisect g goals.toSubarray z1 z2 e1 e2 p1 p2 e
      pure goals
  | none, some _ => throwError "interval_cases failed: could not find lower bound on {e'}"
  | some _, none => throwError "interval_cases failed: could not find upper bound on {e'}"
  | none, none => throwError "interval_cases failed: could not find bounds on {e'}"
end IntervalCases
open IntervalCases
syntax (name := intervalCases) "interval_cases" (ppSpace colGt atomic(binderIdent " : ")? term)?
  (" using " term ", " term)? : tactic
elab_rules : tactic
  | `(tactic| interval_cases $[$[$h :]? $e]? $[using $lb, $ub]?) => do
    let g ← getMainGoal
    let cont x h? subst g e lbs ubs mustUseBounds : TacticM Unit := do
      let goals ← IntervalCases.intervalCases g (.fvar x) e lbs ubs mustUseBounds
      let gs ← goals.mapM fun { goal, .. } => do
        let (fv, g) ← goal.intro1
        let (subst, g) ← substCore g fv (fvarSubst := subst)
        if let some hStx := h.getD none then
          if let some fv := h? then
            g.withContext <| (subst.get fv).addLocalVarInfoForBinderIdent hStx
        pure g
      replaceMainGoal gs.toList
    g.withContext do
    let hName? := (h.getD none).map fun
      | `(binderIdent| $n:ident) => n.getId
      | _ => `_
    match e, lb, ub with
    | e, some lb, some ub =>
      let e ← if let some e := e then Tactic.elabTerm e none else mkFreshExprMVar none
      let lb' ← Tactic.elabTerm lb none
      let ub' ← Tactic.elabTerm ub none
      let lbTy ← inferType lb'
      let ubTy ← inferType ub'
      try
        let (_, hi, _) ← parseBound lbTy
        let .true ← isDefEq e hi | failure
      catch _ => throwErrorAt lb "expected a term of the form _ < {e} or _ ≤ {e}, got {lbTy}"
      try
        let (lo, _) ← parseBound ubTy
        let .true ← isDefEq e lo | failure
      catch _ => throwErrorAt ub "expected a term of the form {e} < _ or {e} ≤ _, got {ubTy}"
      let (subst, xs, g) ← g.generalizeHyp #[{ expr := e, hName? }] (← getFVarIdsAt g)
      g.withContext do
      cont xs[0]! xs[1]? subst g e #[subst.apply lb'] #[subst.apply ub'] (mustUseBounds := true)
    | some e, none, none =>
      let e ← Tactic.elabTerm e none
      let (subst, xs, g) ← g.generalizeHyp #[{ expr := e, hName? }] (← getFVarIdsAt g)
      let x := xs[0]!
      g.withContext do
      let e := subst.apply e
      let mut lbs := #[]
      let mut ubs := #[]
      for ldecl in ← getLCtx do
        try
          let (lo, hi, _) ← parseBound ldecl.type
          if ← withNewMCtxDepth <| withReducible <| isDefEq (.fvar x) lo then
            ubs := ubs.push (.fvar ldecl.fvarId)
          else if ← withNewMCtxDepth <| withReducible <| isDefEq (.fvar x) hi then
            lbs := lbs.push (.fvar ldecl.fvarId)
          else failure
        catch _ => pure ()
      cont x xs[1]? subst g e lbs ubs (mustUseBounds := false)
    | _, _, _ => throwUnsupportedSyntax
end Mathlib.Tactic