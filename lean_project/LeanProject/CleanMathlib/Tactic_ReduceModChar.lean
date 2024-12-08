import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.PowMod
import Mathlib.Tactic.ReduceModChar.Ext
open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq
namespace Tactic
namespace ReduceModChar
open Mathlib.Meta.NormNum
variable {u : Level}
lemma CharP.isInt_of_mod {e' r : ℤ} {α : Type*} [Ring α] {n n' : ℕ} (inst : CharP α n) {e : α}
    (he : IsInt e e') (hn : IsNat n n') (h₂ : IsInt (e' % n') r) : IsInt e r :=
  ⟨by rw [he.out, CharP.intCast_eq_intCast_mod α n, show n = n' from hn.out, h₂.out, Int.cast_id]⟩
lemma CharP.isNat_pow {α} [Semiring α] : ∀ {f : α → ℕ → α} {a : α} {a' b b' c n n' : ℕ},
    CharP α n → f = HPow.hPow → IsNat a a' → IsNat b b' → IsNat n n' →
    Nat.mod (Nat.pow a' b') n' = c → IsNat (f a b) c
  | _, _, a, _, b, _, _, n, _, rfl, ⟨h⟩, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by
    rw [h, Nat.cast_id, Nat.pow_eq, ← Nat.cast_pow, CharP.natCast_eq_natCast_mod α n]
    rfl⟩
attribute [local instance] Mathlib.Meta.monadLiftOptionMetaM in
def normBareNumeral {α : Q(Type u)} (n n' : Q(ℕ)) (pn : Q(IsNat «$n» «$n'»))
    (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
  let ⟨ze, ne, pe⟩ ← Result.toInt _ (← Mathlib.Meta.NormNum.derive e)
  let rr ← evalIntMod.go _ _ ze q(IsInt.raw_refl $ne) _ <|
    .isNat q(instAddMonoidWithOne) _ q(isNat_natCast _ _ (IsNat.raw_refl $n'))
  let ⟨zr, nr, pr⟩ ← rr.toInt _
  return .isInt _ nr zr q(CharP.isInt_of_mod $instCharP $pe $pn $pr)
mutual
  partial def normPow {α : Q(Type u)} (n n' : Q(ℕ)) (pn : Q(IsNat «$n» «$n'»)) (e : Q($α))
      (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
    let .app (.app (f : Q($α → ℕ → $α)) (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
    let .isNat sα na pa ← normIntNumeral' n n' pn a _ instCharP | failure
    let ⟨nb, pb⟩ ← Mathlib.Meta.NormNum.deriveNat b q(instAddMonoidWithOneNat)
    guard <|← withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
    haveI' : $e =Q $a ^ $b := ⟨⟩
    haveI' : $f =Q HPow.hPow := ⟨⟩
    have ⟨c, r⟩ := evalNatPowMod na nb n'
    assumeInstancesCommute
    return .isNat sα c q(CharP.isNat_pow (f := $f) $instCharP (.refl $f) $pa $pb $pn $r)
  partial def normIntNumeral' {α : Q(Type u)} (n n' : Q(ℕ)) (pn : Q(IsNat «$n» «$n'»))
      (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) :=
    normPow n n' pn e _ instCharP <|> normBareNumeral n n' pn e _ instCharP
end
lemma CharP.intCast_eq_mod (R : Type _) [Ring R] (p : ℕ) [CharP R p] (k : ℤ) :
    (k : R) = (k % p : ℤ) := by
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Int.emod_add_ediv]
    _ = ↑(k % p) := by simp [CharP.cast_eq_zero R]
partial def normIntNumeral {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_ : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
  let ⟨n', pn⟩ ← deriveNat n q(instAddMonoidWithOneNat)
  normIntNumeral' n n' pn e _ instCharP
lemma CharP.neg_eq_sub_one_mul {α : Type _} [Ring α] (n : ℕ) (inst : CharP α n) (b : α)
    (a : ℕ) (a' : α) (p : IsNat (n - 1 : α) a) (pa : a = a') :
    -b = a' * b := by
  rw [← pa, ← p.out, ← neg_one_mul]
  simp
@[nolint unusedHavesSuffices] 
partial def normNeg {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app f (b : Q($α)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq f q(Neg.neg (α := $α))
  let r ← (derive (α := α) q($n - 1))
  match r with
  | .isNat sα a p => do
    have : instAddMonoidWithOne =Q $sα := ⟨⟩
    let ⟨a', pa'⟩ ← mkOfNat α sα a
    let pf : Q(-$b = $a' * $b) := q(CharP.neg_eq_sub_one_mul $n $instCharP $b $a $a' $p $pa')
    return { expr := q($a' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNeg: nothing useful to do in negative characteristic"
  | _ => throwError "normNeg: evaluating `{n} - 1` should give an integer result"
lemma CharP.neg_mul_eq_sub_one_mul {α : Type _} [Ring α] (n : ℕ) (inst : CharP α n) (a b : α)
    (na : ℕ) (na' : α) (p : IsNat ((n - 1) * a : α) na) (pa : na = na') :
    -(a * b) = na' * b := by
  rw [← pa, ← p.out, ← neg_one_mul]
  simp
@[nolint unusedHavesSuffices] 
partial def normNegCoeffMul {α : Q(Type u)} (n : Q(ℕ)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app neg (.app (.app mul (a : Q($α))) (b : Q($α))) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq neg q(Neg.neg (α := $α))
  guard <|← withNewMCtxDepth <| isDefEq mul q(HMul.hMul (α := $α))
  let r ← (derive (α := α) q(($n - 1) * $a))
  match r with
  | .isNat sα na np => do
    have : AddGroupWithOne.toAddMonoidWithOne =Q $sα := ⟨⟩
    let ⟨na', npa'⟩ ← mkOfNat α sα na
    let pf : Q(-($a * $b) = $na' * $b) :=
      q(CharP.neg_mul_eq_sub_one_mul $n $instCharP $a $b $na $na' $np $npa')
    return { expr := q($na' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNegCoeffMul: nothing useful to do in negative characteristic"
  | _ => throwError "normNegCoeffMul: evaluating `{n} - 1` should give an integer result"
inductive TypeToCharPResult (α : Q(Type u))
  | intLike (n : Q(ℕ)) (instRing : Q(Ring $α)) (instCharP : Q(CharP $α $n))
  | failure
instance {α : Q(Type u)} : Inhabited (TypeToCharPResult α) := ⟨.failure⟩
partial def typeToCharP (expensive := false) (t : Q(Type u)) : MetaM (TypeToCharPResult t) :=
match Expr.getAppFnArgs t with
| (``ZMod, #[(n : Q(ℕ))]) =>
  return .intLike n
    (q((ZMod.commRing _).toRing) : Q(Ring (ZMod $n)))
    (q(ZMod.charP _) : Q(CharP (ZMod $n) $n))
| (``Polynomial, #[(R : Q(Type u)), _]) => do match ← typeToCharP (expensive := expensive) R with
  | (.intLike n _ _) =>
    return .intLike n
      (q(Polynomial.ring) : Q(Ring (Polynomial $R)))
      (q(Polynomial.instCharP _) : Q(CharP (Polynomial $R) $n))
  | .failure => return .failure
| _ => if ! expensive then return .failure else do
  withNewMCtxDepth do
    let .some instRing ← trySynthInstanceQ q(Ring $t) | return .failure
    let n ← mkFreshExprMVarQ q(ℕ)
    let .some instCharP ← findLocalDeclWithType? q(CharP $t $n) | return .failure
    return .intLike (← instantiateMVarsQ n) instRing (.fvar instCharP)
partial def matchAndNorm (expensive := false) (e : Expr) : MetaM Simp.Result := do
  let α ← inferType e
  let u_succ : Level ← getLevel α
  let (.succ u) := u_succ | throwError "expected {α} to be a `Type _`, not `Sort {u_succ}`"
  have α : Q(Type u) := α
  match ← typeToCharP (expensive := expensive) α with
    | (.intLike n instRing instCharP) =>
      normIntNumeral n e instRing instCharP >>= Result.toSimpResult <|>
      normNegCoeffMul n e instRing instCharP <|> 
      normNeg n e instRing instCharP 
    | .failure =>
      throwError "inferred type `{α}` does not have a known characteristic"
attribute [reduce_mod_char] sub_eq_add_neg
attribute [reduce_mod_char] zero_add add_zero zero_mul mul_zero one_mul mul_one
attribute [reduce_mod_char] eq_self_iff_true 
partial def derive (expensive := false) (e : Expr) : MetaM Simp.Result := do
  withTraceNode `Tactic.reduce_mod_char (fun _ => return m!"{e}") do
  let e ← instantiateMVars e
  let config : Simp.Config := {
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ext? ← getSimpExtension? `reduce_mod_char
  let ext ← match ext? with
  | some ext => pure ext
  | none => throwError "internal error: reduce_mod_char not registered as simp extension"
  let ctx ← Simp.mkContext config (congrTheorems := congrTheorems)
    (simpTheorems := #[← ext.getTheorems])
  let discharge := Mathlib.Meta.NormNum.discharge ctx
  let r : Simp.Result := {expr := e}
  let pre := Simp.preDefault #[] >> fun e =>
      try return (Simp.Step.done (← matchAndNorm (expensive := expensive) e))
      catch _ => pure .continue
  let post := Simp.postDefault #[]
  let r ← r.mkEqTrans (← Simp.main r.expr ctx (methods := { pre, post, discharge? := discharge })).1
  return r
partial def reduceModCharTarget (expensive := false) : TacticM Unit := do
  liftMetaTactic1 fun goal ↦ do
    let tgt ← instantiateMVars (← goal.getType)
    let prf ← derive (expensive := expensive) tgt
    if prf.expr.consumeMData.isConstOf ``True then
      match prf.proof? with
      | some proof => goal.assign (← mkOfEqTrue proof)
      | none => goal.assign (mkConst ``True.intro)
      return none
    else
      applySimpResultToTarget goal tgt prf
partial def reduceModCharHyp (expensive := false) (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun goal ↦ do
    let hyp ← instantiateMVars (← fvarId.getDecl).type
    let prf ← derive (expensive := expensive) hyp
    return (← applySimpResultToLocalDecl goal fvarId prf false).map (·.snd)
open Parser.Tactic Elab.Tactic
syntax (name := reduce_mod_char) "reduce_mod_char" (location)? : tactic
@[inherit_doc reduce_mod_char]
syntax (name := reduce_mod_char!) "reduce_mod_char!" (location)? : tactic
elab_rules : tactic
| `(tactic| reduce_mod_char $[$loc]?) => unsafe do
  match expandOptLocation (Lean.mkOptionalNode loc) with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM reduceModCharHyp
    if target then reduceModCharTarget
  | Location.wildcard => do
    (← (← getMainGoal).getNondepPropHyps).forM reduceModCharHyp
    reduceModCharTarget
| `(tactic| reduce_mod_char! $[$loc]?) => unsafe do
  match expandOptLocation (Lean.mkOptionalNode loc) with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM (reduceModCharHyp (expensive := true))
    if target then reduceModCharTarget (expensive := true)
  | Location.wildcard => do
    (← (← getMainGoal).getNondepPropHyps).forM (reduceModCharHyp (expensive := true))
    reduceModCharTarget (expensive := true)
end ReduceModChar
end Tactic