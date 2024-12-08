import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Util.SynthesizeUsing
open Lean Elab Tactic Meta Qq Mathlib
initialize registerTraceClass `linarith
initialize registerTraceClass `linarith.detail
namespace Linarith
def linarithTraceProofs {α} [ToMessageData α] (s : α) (l : List Expr) : MetaM Unit := do
  trace[linarith] "{s}"
  trace[linarith] (← l.mapM fun e => do instantiateMVars (← inferType e))
abbrev Linexp : Type := List (Nat × Int)
namespace Linexp
partial def add : Linexp → Linexp → Linexp
| [], a => a
| a, [] => a
| (a@(n1,z1)::t1), (b@(n2,z2)::t2) =>
  if n1 < n2 then b::add (a::t1) t2
  else if n2 < n1 then a::add t1 (b::t2)
  else
    let sum := z1 + z2
    if sum = 0 then add t1 t2 else (n1, sum)::add t1 t2
def scale (c : Int) (l : Linexp) : Linexp :=
  if c = 0 then []
  else if c = 1 then l
  else l.map fun ⟨n, z⟩ => (n, z*c)
def get (n : Nat) : Linexp → Option Int
  | [] => none
  | ((a, b)::t) =>
    if a < n then none
    else if a = n then some b
    else get n t
def contains (n : Nat) : Linexp → Bool := Option.isSome ∘ get n
def zfind (n : Nat) (l : Linexp) : Int :=
  match l.get n with
  | none => 0
  | some v => v
def vars (l : Linexp) : List Nat :=
  l.map Prod.fst
def cmp : Linexp → Linexp → Ordering
  | [], [] => Ordering.eq
  | [], _ => Ordering.lt
  | _, [] => Ordering.gt
  | ((n1,z1)::t1), ((n2,z2)::t2) =>
    if n1 < n2 then Ordering.lt
    else if n2 < n1 then Ordering.gt
    else if z1 < z2 then Ordering.lt
    else if z2 < z1 then Ordering.gt
    else cmp t1 t2
end Linexp
structure Comp : Type where
  str : Ineq
  coeffs : Linexp
deriving Inhabited, Repr
def Comp.vars : Comp → List Nat := Linexp.vars ∘ Comp.coeffs
def Comp.coeffOf (c : Comp) (a : Nat) : Int :=
  c.coeffs.zfind a
def Comp.scale (c : Comp) (n : Nat) : Comp :=
  { c with coeffs := c.coeffs.scale n }
def Comp.add (c1 c2 : Comp) : Comp :=
  ⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩
def Comp.cmp : Comp → Comp → Ordering
  | ⟨str1, coeffs1⟩, ⟨str2, coeffs2⟩ =>
    match str1.cmp str2 with
    | Ordering.lt => Ordering.lt
    | Ordering.gt => Ordering.gt
    | Ordering.eq => coeffs1.cmp coeffs2
def Comp.isContr (c : Comp) : Bool := c.coeffs.isEmpty && c.str = Ineq.lt
instance Comp.ToFormat : ToFormat Comp :=
  ⟨fun p => format p.coeffs ++ toString p.str ++ "0"⟩
structure Preprocessor : Type where
  name : String
  transform : Expr → MetaM (List Expr)
structure GlobalPreprocessor : Type where
  name : String
  transform : List Expr → MetaM (List Expr)
def Branch : Type := MVarId × List Expr
structure GlobalBranchingPreprocessor : Type where
  name : String
  transform : MVarId → List Expr → MetaM (List Branch)
def Preprocessor.globalize (pp : Preprocessor) : GlobalPreprocessor where
  name := pp.name
  transform := List.foldrM (fun e ret => do return (← pp.transform e) ++ ret) []
def GlobalPreprocessor.branching (pp : GlobalPreprocessor) : GlobalBranchingPreprocessor where
  name := pp.name
  transform := fun g l => do return [⟨g, ← pp.transform l⟩]
def GlobalBranchingPreprocessor.process (pp : GlobalBranchingPreprocessor)
    (g : MVarId) (l : List Expr) : MetaM (List Branch) := g.withContext do
  let branches ← pp.transform g l
  if branches.length > 1 then
    trace[linarith] "Preprocessing: {pp.name} has branched, with branches:"
  for ⟨goal, hyps⟩ in branches do
    goal.withContext do
      linarithTraceProofs m!"Preprocessing: {pp.name}" hyps
  return branches
instance PreprocessorToGlobalBranchingPreprocessor :
    Coe Preprocessor GlobalBranchingPreprocessor :=
  ⟨GlobalPreprocessor.branching ∘ Preprocessor.globalize⟩
instance GlobalPreprocessorToGlobalBranchingPreprocessor :
    Coe GlobalPreprocessor GlobalBranchingPreprocessor :=
  ⟨GlobalPreprocessor.branching⟩
structure CertificateOracle : Type where
  produceCertificate (hyps : List Comp) (max_var : Nat) : MetaM (Std.HashMap Nat Nat)
def parseCompAndExpr (e : Expr) : MetaM (Ineq × Expr) := do
  let (rel, _, e, z) ← e.ineq?
  if z.zero? then return (rel, e) else throwError "invalid comparison, rhs not zero: {z}"
def mkSingleCompZeroOf (c : Nat) (h : Expr) : MetaM (Ineq × Expr) := do
  let tp ← inferType h
  let (iq, e) ← parseCompAndExpr tp
  if c = 0 then do
    let e' ← mkAppM ``zero_mul #[e]
    return (Ineq.eq, e')
  else if c = 1 then return (iq, h)
  else do
    let (_, tp, _) ← tp.ineq?
    let cpos : Q(Prop) ← mkAppM ``GT.gt #[(← tp.ofNat c), (← tp.ofNat 0)]
    let ex ← synthesizeUsingTactic' cpos (← `(tactic| norm_num))
    let e' ← mkAppM iq.toConstMulName #[h, ex]
    return (iq, e')
end Linarith