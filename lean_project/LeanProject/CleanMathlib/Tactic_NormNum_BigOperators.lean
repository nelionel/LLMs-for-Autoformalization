import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.List.FinRange
namespace Mathlib.Meta
open Lean
open Meta
open Qq
variable {u v : Level}
inductive Nat.UnifyZeroOrSuccResult (n : Q(ℕ))
  | zero (pf : $n =Q 0)
  | succ (n' : Q(ℕ)) (pf : $n =Q Nat.succ $n')
def Nat.unifyZeroOrSucc (n : Q(ℕ)) : MetaM (Nat.UnifyZeroOrSuccResult n) := do
  match ← isDefEqQ n q(0) with
  | .defEq pf => return .zero pf
  | .notDefEq => do
    let n' : Q(ℕ) ← mkFreshExprMVar q(ℕ)
    let ⟨(_pf : $n =Q Nat.succ $n')⟩ ← assertDefEqQ n q(Nat.succ $n')
    let (.some (n'_val : Q(ℕ))) ← getExprMVarAssignment? n'.mvarId! |
      throwError "could not figure out value of `?n` from `{n} =?= Nat.succ ?n`"
    pure (.succ n'_val ⟨⟩)
inductive List.ProveNilOrConsResult {α : Q(Type u)} (s : Q(List $α))
  | nil (pf : Q($s = []))
  | cons (a : Q($α)) (s' : Q(List $α)) (pf : Q($s = List.cons $a $s'))
def List.ProveNilOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(List $α)) (t : Q(List $β)) :
    List.ProveNilOrConsResult s → List.ProveNilOrConsResult t
  | .nil pf => .nil pf
  | .cons a s' pf => .cons a s' pf
def List.ProveNilOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(List $α)}
    (eq : Q($s = $t)) :
    List.ProveNilOrConsResult t → List.ProveNilOrConsResult s
  | .nil pf => .nil q(Eq.trans $eq $pf)
  | .cons a s' pf => .cons a s' q(Eq.trans $eq $pf)
lemma List.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    List.range n = [] := by rw [pn.out, Nat.cast_zero, List.range_zero]
lemma List.range_succ_eq_map' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    List.range n = 0 :: List.map Nat.succ (List.range n') := by
  rw [pn.out, Nat.cast_id, pn', List.range_succ_eq_map]
set_option linter.unusedVariables false in
partial def List.proveNilOrCons {u : Level} {α : Q(Type u)} (s : Q(List $α)) :
    MetaM (List.ProveNilOrConsResult s) :=
  s.withApp fun e a =>
  match (e, e.constName, a) with
  | (_, ``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.nil q(.refl []))
  | (_, ``List.nil, _) => haveI : $s =Q [] := ⟨⟩; pure (.nil q(rfl))
  | (_, ``List.cons, #[_, (a : Q($α)), (s' : Q(List $α))]) =>
    haveI : $s =Q $a :: $s' := ⟨⟩; pure (.cons a s' q(rfl))
  | (_, ``List.range, #[(n : Q(ℕ))]) =>
    have s : Q(List ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveNilOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI' : $nn =Q 0 := ⟨⟩
      return .nil q(List.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      have : $nn =Q .succ $n' := ⟨⟩
      return .cons _ _ q(List.range_succ_eq_map' $pn (.refl $nn))
  | (_, ``List.finRange, #[(n : Q(ℕ))]) =>
    have s : Q(List (Fin $n)) := s
    .uncheckedCast _ _ <$> show MetaM (ProveNilOrConsResult s) from do
    haveI' : $s =Q .finRange $n := ⟨⟩
    return match ← Nat.unifyZeroOrSucc n with 
    | .zero _pf => .nil q(List.finRange_zero)
    | .succ n' _pf => .cons _ _ q(List.finRange_succ_eq_map $n')
  | (.const ``List.map [v, _], _, #[(β : Q(Type v)), _, (f : Q($β → $α)), (xxs : Q(List $β))]) => do
    haveI' : $s =Q ($xxs).map $f := ⟨⟩
    return match ← List.proveNilOrCons xxs with
    | .nil pf => .nil q(($pf ▸ List.map_nil : List.map _ _ = _))
    | .cons x xs pf => .cons q($f $x) q(($xs).map $f)
      q(($pf ▸ List.map_cons $f $x $xs : List.map _ _ = _))
  | (_, fn, args) =>
    throwError "List.proveNilOrCons: unsupported List expression {s} ({fn}, {args})"
inductive Multiset.ProveZeroOrConsResult {α : Q(Type u)} (s : Q(Multiset $α))
  | zero (pf : Q($s = 0))
  | cons (a : Q($α)) (s' : Q(Multiset $α)) (pf : Q($s = Multiset.cons $a $s'))
def Multiset.ProveZeroOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(Multiset $α)) (t : Q(Multiset $β)) :
    Multiset.ProveZeroOrConsResult s → Multiset.ProveZeroOrConsResult t
  | .zero pf => .zero pf
  | .cons a s' pf => .cons a s' pf
def Multiset.ProveZeroOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(Multiset $α)}
    (eq : Q($s = $t)) :
    Multiset.ProveZeroOrConsResult t → Multiset.ProveZeroOrConsResult s
  | .zero pf => .zero q(Eq.trans $eq $pf)
  | .cons a s' pf => .cons a s' q(Eq.trans $eq $pf)
lemma Multiset.insert_eq_cons {α : Type*} (a : α) (s : Multiset α) :
    insert a s = Multiset.cons a s :=
  rfl
lemma Multiset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Multiset.range n = 0 := by rw [pn.out, Nat.cast_zero, Multiset.range_zero]
lemma Multiset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Multiset.range n = n' ::ₘ Multiset.range n' := by
  rw [pn.out, Nat.cast_id, pn', Multiset.range_succ]
partial def Multiset.proveZeroOrCons {α : Q(Type u)} (s : Q(Multiset $α)) :
    MetaM (Multiset.ProveZeroOrConsResult s) :=
  match s.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.zero q(rfl))
  | (``Zero.zero, _) => haveI : $s =Q 0 := ⟨⟩; pure (.zero q(rfl))
  | (``Multiset.cons, #[_, (a : Q($α)), (s' : Q(Multiset $α))]) =>
    haveI : $s =Q .cons $a $s' := ⟨⟩
    pure (.cons a s' q(rfl))
  | (``Multiset.ofList, #[_, (val : Q(List $α))]) => do
    haveI : $s =Q .ofList $val := ⟨⟩
    return match ← List.proveNilOrCons val with
    | .nil pf => .zero q($pf ▸ Multiset.coe_nil : Multiset.ofList _ = _)
    | .cons a s' pf => .cons a q($s') q($pf ▸ Multiset.cons_coe $a $s' : Multiset.ofList _ = _)
  | (``Multiset.range, #[(n : Q(ℕ))]) => do
    have s : Q(Multiset ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveZeroOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI' : $nn =Q 0 := ⟨⟩
      return .zero q(Multiset.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      haveI' : $nn =Q ($n').succ := ⟨⟩
      return .cons _ _ q(Multiset.range_succ' $pn rfl)
  | (fn, args) =>
    throwError "Multiset.proveZeroOrCons: unsupported multiset expression {s} ({fn}, {args})"
inductive Finset.ProveEmptyOrConsResult {α : Q(Type u)} (s : Q(Finset $α))
  | empty (pf : Q($s = ∅))
  | cons (a : Q($α)) (s' : Q(Finset $α)) (h : Q($a ∉ $s')) (pf : Q($s = Finset.cons $a $s' $h))
def Finset.ProveEmptyOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(Finset $α)) (t : Q(Finset $β)) :
    Finset.ProveEmptyOrConsResult s → Finset.ProveEmptyOrConsResult t
  | .empty pf => .empty pf
  | .cons a s' h pf => .cons a s' h pf
def Finset.ProveEmptyOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(Finset $α)}
    (eq : Q($s = $t)) :
    Finset.ProveEmptyOrConsResult t → Finset.ProveEmptyOrConsResult s
  | .empty pf => .empty q(Eq.trans $eq $pf)
  | .cons a s' h pf => .cons a s' h q(Eq.trans $eq $pf)
lemma Finset.insert_eq_cons {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (h : a ∉ s) :
    insert a s = Finset.cons a s h := by
  ext; simp
lemma Finset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Finset.range n = {} := by rw [pn.out, Nat.cast_zero, Finset.range_zero]
lemma Finset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Finset.range n = Finset.cons n' (Finset.range n') Finset.not_mem_range_self := by
  rw [pn.out, Nat.cast_id, pn', Finset.range_succ, Finset.insert_eq_cons]
lemma Finset.univ_eq_elems {α : Type*} [Fintype α] (elems : Finset α)
    (complete : ∀ x : α, x ∈ elems) :
    Finset.univ = elems := by
  ext x; simpa using complete x
partial def Finset.proveEmptyOrCons {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (ProveEmptyOrConsResult s) :=
  match s.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.empty q(rfl))
  | (``Finset.cons, #[_, (a : Q($α)), (s' : Q(Finset $α)), (h : Q(¬ $a ∈ $s'))]) =>
    haveI : $s =Q .cons $a $s' $h := ⟨⟩
    pure (.cons a s' h q(.refl $s))
  | (``Finset.mk, #[_, (val : Q(Multiset $α)), (nd : Q(Multiset.Nodup $val))]) => do
    match ← Multiset.proveZeroOrCons val with
    | .zero pf => pure <| .empty (q($pf ▸ Finset.mk_zero) : Q(Finset.mk $val $nd = ∅))
    | .cons a s' pf => do
      let h : Q(Multiset.Nodup ($a ::ₘ $s')) := q($pf ▸ $nd)
      let nd' : Q(Multiset.Nodup $s') := q((Multiset.nodup_cons.mp $h).2)
      let h' : Q($a ∉ $s') := q((Multiset.nodup_cons.mp $h).1)
      return (.cons a q(Finset.mk $s' $nd') h'
        (q($pf ▸ Finset.mk_cons $h) : Q(Finset.mk $val $nd = Finset.cons $a ⟨$s', $nd'⟩ $h')))
  | (``Finset.range, #[(n : Q(ℕ))]) =>
    have s : Q(Finset ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveEmptyOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI : $nn =Q 0 := ⟨⟩
      return .empty q(Finset.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      haveI' : $nn =Q ($n').succ := ⟨⟩
      return .cons n' _ _ q(Finset.range_succ' $pn (.refl $nn))
  | (``Finset.univ, #[_, (instFT : Q(Fintype $α))]) => do
    haveI' : $s =Q .univ := ⟨⟩
    match (← whnfI instFT).getAppFnArgs with
    | (``Fintype.mk, #[_, (elems : Q(Finset $α)), (complete : Q(∀ x : $α, x ∈ $elems))]) => do
      let res ← Finset.proveEmptyOrCons elems
      pure <| res.eq_trans q(Finset.univ_eq_elems $elems $complete)
    | e =>
      throwError "Finset.proveEmptyOrCons: could not determine elements of Fintype instance {e}"
  | (fn, args) =>
    throwError "Finset.proveEmptyOrCons: unsupported finset expression {s} ({fn}, {args})"
namespace NormNum
def Result.eq_trans {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b)) : Result b → Result a
  | .isBool true proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q($b) := proof
    Result.isTrue (x := a) q($eq ▸ $proof)
  | .isBool false proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q(¬ $b) := proof
  Result.isFalse (x := a) q($eq ▸ $proof)
  | .isNat inst lit proof => Result.isNat inst lit q($eq ▸ $proof)
  | .isNegNat inst lit proof => Result.isNegNat inst lit q($eq ▸ $proof)
  | .isRat inst q n d proof => Result.isRat inst q n d q($eq ▸ $proof)
protected lemma Finset.sum_empty {β α : Type*} [CommSemiring β] (f : α → β) :
    IsNat (Finset.sum ∅ f) 0 :=
  ⟨by simp⟩
protected lemma Finset.prod_empty {β α : Type*} [CommSemiring β] (f : α → β) :
    IsNat (Finset.prod ∅ f) 1 :=
  ⟨by simp⟩
partial def evalFinsetBigop {α : Q(Type u)} {β : Q(Type v)}
    (op : Q(Finset $α → ($α → $β) → $β))
    (f : Q($α → $β))
    (res_empty : Result q($op Finset.empty $f))
    (res_cons : {a : Q($α)} -> {s' : Q(Finset $α)} -> {h : Q($a ∉ $s')} ->
      Result (α := β) q($f $a) -> Result (α := β) q($op $s' $f) ->
      MetaM (Result (α := β) q($op (Finset.cons $a $s' $h) $f))) :
    (s : Q(Finset $α)) → MetaM (Result (α := β) q($op $s $f))
  | s => do
    match ← Finset.proveEmptyOrCons s with
    | .empty pf => pure <| res_empty.eq_trans q(congr_fun (congr_arg _ $pf) _)
    | .cons a s' h pf => do
      let fa : Q($β) := Expr.betaRev f #[a]
      let res_fa ← derive fa
      let res_op_s' : Result q($op $s' $f) ← evalFinsetBigop op f res_empty @res_cons s'
      let res ← res_cons res_fa res_op_s'
      let eq : Q($op $s $f = $op (Finset.cons $a $s' $h) $f) := q(congr_fun (congr_arg _ $pf) _)
      pure (res.eq_trans eq)
attribute [local instance] monadLiftOptionMetaM in
@[norm_num @Finset.prod _ _ _ _ _]
partial def evalFinsetProd : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const ``Finset.prod [v, _]) α) β') _) s) f ←
    whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS : Q(CommSemiring $β) ← synthInstanceQ q(CommSemiring $β) <|>
    throwError "not a commutative semiring: {β}"
  let instS : Q(Semiring $β) := q(CommSemiring.toSemiring)
  let n : Q(ℕ) := .lit (.natVal 1)
  let pf : Q(IsNat (Finset.prod ∅ $f) $n) := q(@Finset.prod_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf
  evalFinsetBigop q(Finset.prod) f res_empty (fun {a s' h} res_fa res_prod_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res ← evalMul.core q($fa * Finset.prod $s' $f) q(HMul.hMul) _ _ instS res_fa
        res_prod_s'
      let eq : Q(Finset.prod (Finset.cons $a $s' $h) $f = $fa * Finset.prod $s' $f) :=
        q(Finset.prod_cons $h)
      pure <| res.eq_trans eq)
    s
attribute [local instance] monadLiftOptionMetaM in
@[norm_num @Finset.sum _ _ _ _ _]
partial def evalFinsetSum : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const ``Finset.sum [v, _]) α) β') _) s) f ←
    whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS : Q(CommSemiring $β) ← synthInstanceQ q(CommSemiring $β) <|>
    throwError "not a commutative semiring: {β}"
  let n : Q(ℕ) := mkRawNatLit 0
  let pf : Q(IsNat (Finset.sum ∅ $f) $n) := q(@Finset.sum_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf
  evalFinsetBigop q(Finset.sum) f res_empty (fun {a s' h} res_fa res_sum_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res ← evalAdd.core q($fa + Finset.sum $s' $f) q(HAdd.hAdd) _ _ res_fa res_sum_s'
      let eq : Q(Finset.sum (Finset.cons $a $s' $h) $f = $fa + Finset.sum $s' $f) :=
        q(Finset.sum_cons $h)
      pure <| res.eq_trans eq)
    s
end NormNum
end Meta
end Mathlib