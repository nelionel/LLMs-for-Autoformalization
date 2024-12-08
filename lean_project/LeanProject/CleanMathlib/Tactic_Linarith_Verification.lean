import Mathlib.Tactic.Linarith.Parsing
import Mathlib.Util.Qq
open Lean Elab Tactic Meta Mathlib
namespace Qq
variable {u : Level}
def ofNatQ (α : Q(Type $u)) (_ : Q(Semiring $α)) (n : ℕ) : Q($α) :=
  match n with
  | 0 => q(0 : $α)
  | 1 => q(1 : $α)
  | k+2 =>
    have lit : Q(ℕ) := mkRawNatLit n
    have k : Q(ℕ) := mkRawNatLit k
    haveI : $lit =Q $k + 2 := ⟨⟩
    q(OfNat.ofNat $lit)
end Qq
namespace Linarith
open Ineq
open Qq
def mulExpr' {u : Level} (n : ℕ) {α : Q(Type $u)} (inst : Q(Semiring $α)) (e : Q($α)) : Q($α) :=
  if n = 1 then e else
    let n := ofNatQ α inst n
    q($n * $e)
def mulExpr (n : ℕ) (e : Expr) : MetaM Expr := do
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let inst : Q(Semiring $α) ← synthInstanceQ q(Semiring $α)
  return mulExpr' n inst e
def addExprs' {u : Level} {α : Q(Type $u)} (_inst : Q(AddMonoid $α)) : List Q($α) → Q($α)
  | []   => q(0)
  | h::t => go h t
    where
    go (p : Q($α)) : List Q($α) → Q($α)
    | [] => p
    | [q] => q($p + $q)
    | q::t => go q($p + $q) t
def addExprs : List Expr → MetaM Expr
  | [] => return q(0) 
  | L@(h::_) => do
    let ⟨_, α, _⟩ ← inferTypeQ' h
    let inst : Q(AddMonoid $α) ← synthInstanceQ q(AddMonoid $α)
    return addExprs' inst L
def addIneq : Ineq → Ineq → (Name × Ineq)
  | eq, eq => (``Linarith.eq_of_eq_of_eq, eq)
  | eq, le => (``Linarith.le_of_eq_of_le, le)
  | eq, lt => (``Linarith.lt_of_eq_of_lt, lt)
  | le, eq => (``Linarith.le_of_le_of_eq, le)
  | le, le => (``Linarith.add_nonpos, le)
  | le, lt => (``Linarith.add_lt_of_le_of_neg, lt)
  | lt, eq => (``Linarith.lt_of_lt_of_eq, lt)
  | lt, le => (``Linarith.add_lt_of_neg_of_le, lt)
  | lt, lt => (``Linarith.add_neg, lt)
def mkLTZeroProof : List (Expr × ℕ) → MetaM Expr
  | [] => throwError "no linear hypotheses found"
  | [(h, c)] => do
      let (_, t) ← mkSingleCompZeroOf c h
      return t
  | ((h, c)::t) => do
      let (iq, h') ← mkSingleCompZeroOf c h
      let (_, t) ← t.foldlM (fun pr ce ↦ step pr.1 pr.2 ce.1 ce.2) (iq, h')
      return t
  where
    step (c : Ineq) (pf npf : Expr) (coeff : ℕ) : MetaM (Ineq × Expr) := do
      let (iq, h') ← mkSingleCompZeroOf coeff npf
      let (nm, niq) := addIneq c iq
      return (niq, ← mkAppM nm #[pf, h'])
def leftOfIneqProof (prf : Expr) : MetaM Expr := do
  let (_, _, t, _) ← (← inferType prf).ineq?
  return t
def typeOfIneqProof (prf : Expr) : MetaM Expr := do
  let (_, ty, _) ← (← inferType prf).ineq?
  return ty
def mkNegOneLtZeroProof (tp : Expr) : MetaM Expr := do
  let zero_lt_one ← mkAppOptM ``Linarith.zero_lt_one #[tp, none]
  mkAppM `neg_neg_of_pos #[zero_lt_one]
def addNegEqProofs : List Expr → MetaM (List Expr)
  | [] => return []
  | (h::tl) => do
    let (iq, t) ← parseCompAndExpr (← inferType h)
    match iq with
    | Ineq.eq => do
      let nep := mkAppN (← mkAppM `Iff.mpr #[← mkAppOptM ``neg_eq_zero #[none, none, t]]) #[h]
      let tl ← addNegEqProofs tl
      return h::nep::tl
    | _ => return h :: (← addNegEqProofs tl)
def proveEqZeroUsing (tac : TacticM Unit) (e : Expr) : MetaM Expr := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  let _h : Q(Zero $α) ← synthInstanceQ q(Zero $α)
  synthesizeUsing' q($e = 0) tac
def proveFalseByLinarith (transparency : TransparencyMode) (oracle : CertificateOracle)
    (discharger : TacticM Unit) : MVarId → List Expr → MetaM Expr
  | _, [] => throwError "no args to linarith"
  | g, l@(h::_) => do
      trace[linarith.detail] "Beginning work in `proveFalseByLinarith`."
      Lean.Core.checkSystem decl_name%.toString
      let l' ← addNegEqProofs l
      trace[linarith.detail] "... finished `addNegEqProofs`."
      let inputs := (← mkNegOneLtZeroProof (← typeOfIneqProof h))::l'.reverse
      trace[linarith.detail] "... finished `mkNegOneLtZeroProof`."
      trace[linarith.detail] (← inputs.mapM inferType)
      let (comps, max_var) ← linearFormsAndMaxVar transparency inputs
      trace[linarith.detail] "... finished `linearFormsAndMaxVar`."
      trace[linarith.detail] "{comps}"
      let certificate : Std.HashMap Nat Nat ← try
        oracle.produceCertificate comps max_var
      catch e =>
        trace[linarith] e.toMessageData
        throwError "linarith failed to find a contradiction"
      trace[linarith] "linarith has found a contradiction: {certificate.toList}"
      let enum_inputs := inputs.enum
      let zip := enum_inputs.filterMap fun ⟨n, e⟩ => (certificate[n]?).map (e, ·)
      let mls ← zip.mapM fun ⟨e, n⟩ => do mulExpr n (← leftOfIneqProof e)
      let sm ← addExprs mls
      trace[linarith] "The expression\n  {sm}\nshould be both 0 and negative"
      let sm_eq_zero ← proveEqZeroUsing discharger sm
      let sm_lt_zero ← mkLTZeroProof zip
      let pftp ← inferType sm_lt_zero
      let ⟨_, nep, _⟩ ← g.rewrite pftp sm_eq_zero
      let pf' ← mkAppM ``Eq.mp #[nep, sm_lt_zero]
      mkAppM ``Linarith.lt_irrefl #[pf']
end Linarith