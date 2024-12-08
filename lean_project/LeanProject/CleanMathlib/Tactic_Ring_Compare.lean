import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.NormNum.Ineq
namespace Mathlib.Tactic.Ring
open Lean Qq Meta
section Typeclass
abbrev cs_of_ocs (α : Type*) [OrderedCommSemiring α] : CommSemiring α := inferInstance
abbrev amwo_of_ocs (α : Type*) [OrderedCommSemiring α] : AddMonoidWithOne α := inferInstance
abbrev le_of_ocs (α : Type*) [OrderedCommSemiring α] : LE α := inferInstance
abbrev cs_of_socs (α : Type*) [StrictOrderedCommSemiring α] : CommSemiring α := inferInstance
abbrev amwo_of_socs (α : Type*) [StrictOrderedCommSemiring α] : AddMonoidWithOne α := inferInstance
abbrev lt_of_socs (α : Type*) [StrictOrderedCommSemiring α] : LT α := inferInstance
end Typeclass
section Lemma
theorem add_le_add_right {α : Type*} [OrderedCommSemiring α] {b c : α} (bc : b ≤ c) (a : α) :
    b + a ≤ c + a :=
  _root_.add_le_add_right bc a
theorem add_le_of_nonpos_left {α : Type*} [OrderedCommSemiring α] (a : α) {b : α} (h : b ≤ 0) :
    b + a ≤ a :=
  _root_.add_le_of_nonpos_left h
theorem le_add_of_nonneg_left {α : Type*} [OrderedCommSemiring α] (a : α) {b : α} (h : 0 ≤ b) :
    a ≤ b + a :=
  _root_.le_add_of_nonneg_left h
theorem add_lt_add_right {α : Type*} [StrictOrderedCommSemiring α] {b c : α} (bc : b < c) (a : α) :
    b + a < c + a :=
  _root_.add_lt_add_right bc a
theorem add_lt_of_neg_left {α : Type*} [StrictOrderedCommSemiring α] (a : α) {b : α} (h : b < 0) :
    b + a < a :=
  _root_.add_lt_of_neg_left a h
theorem lt_add_of_pos_left {α : Type*} [StrictOrderedCommSemiring α] (a : α) {b : α} (h : 0 < b) :
    a < b + a :=
  _root_.lt_add_of_pos_left a h
end Lemma
inductive ExceptType | tooSmall | notComparable
export ExceptType (tooSmall notComparable)
def evalLE {v : Level} {α : Q(Type v)} (_ : Q(OrderedCommSemiring $α)) {a b : Q($α)}
    (va : Ring.ExSum q(cs_of_ocs $α) a) (vb : Ring.ExSum q(cs_of_ocs $α) b) :
    MetaM (Except ExceptType Q($a ≤ $b)) := do
  let lα : Q(LE $α) := q(le_of_ocs $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(amwo_of_ocs $α) (mkRawNatLit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(amwo_of_ocs $α) (mkRawNatLit 0) (q(NormNum.isNat_ofNat $α $pz):)
  match va, vb with
  | .zero, .zero => pure <| .ok (q(le_refl (0:$α)):)
  | .add (b := a') (.const (e := xa) ca hypa) va', .add (.const (e := xb) cb hypb) vb' => do
    unless va'.eq vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rxb | return .error tooSmall
    pure <| .ok (q(add_le_add_right (a := $a') $pf):)
  | .add (.const (e := xa) ca hypa) va', _ => do
    unless va'.eq vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rxa rz | return .error tooSmall
    pure <| .ok (q(add_le_of_nonpos_left (a := $b) $pf):)
  | _, .add (.const (e := xb) cb hypb) vb' => do
    unless va.eq vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLE.core lα rz rxb | return .error tooSmall
    pure <| .ok (q(le_add_of_nonneg_left (a := $a) $pf):)
  | _, _ =>
    unless va.eq vb do return .error notComparable
    pure <| .ok (q(le_refl $a):)
def evalLT {v : Level} {α : Q(Type v)} (_ : Q(StrictOrderedCommSemiring $α)) {a b : Q($α)}
    (va : Ring.ExSum q(cs_of_socs $α) a) (vb : Ring.ExSum q(cs_of_socs $α) b) :
    MetaM (Except ExceptType Q($a < $b)) := do
  let lα : Q(LT $α) := q(lt_of_socs $α)
  assumeInstancesCommute
  let ⟨_, pz⟩ ← NormNum.mkOfNat α q(amwo_of_socs $α) (mkRawNatLit 0)
  let rz : NormNum.Result q((0:$α)) :=
    NormNum.Result.isNat q(amwo_of_socs $α) (mkRawNatLit 0) (q(NormNum.isNat_ofNat $α $pz):)
  match va, vb with
  | .zero, .zero => return .error tooSmall
  | .add (b := a') (.const (e := xa) ca hypa) va', .add (.const (e := xb) cb hypb) vb' => do
    unless va'.eq vb' do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rxb | return .error tooSmall
    pure <| .ok (q(add_lt_add_right $pf $a'):)
  | .add (.const (e := xa) ca hypa) va', _ => do
    unless va'.eq vb do return .error notComparable
    let rxa := NormNum.Result.ofRawRat ca xa hypa
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rxa rz | return .error tooSmall
    have pf : Q($xa < 0) := pf
    pure <| .ok (q(add_lt_of_neg_left $b $pf):)
  | _, .add (.const (e := xb) cb hypb) vb' => do
    unless va.eq vb' do return .error notComparable
    let rxb := NormNum.Result.ofRawRat cb xb hypb
    let NormNum.Result.isTrue pf ← NormNum.evalLT.core lα rz rxb | return .error tooSmall
    pure <| .ok (q(lt_add_of_pos_left $a $pf):)
  | _, _ => return .error notComparable
theorem le_congr {α : Type*} [LE α] {a b c d : α} (h1 : a = b) (h2 : b ≤ c) (h3 : d = c) :
    a ≤ d := by
  rwa [h1, h3]
theorem lt_congr {α : Type*} [LT α] {a b c d : α} (h1 : a = b) (h2 : b < c) (h3 : d = c) :
    a < d := by
  rwa [h1, h3]
attribute [local instance] monadLiftOptionMetaM in
def proveLE (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).le?
    | throwError "ring failed: not of the form `A ≤ B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ← synthInstanceQ q(OrderedCommSemiring $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← mkCache q(cs_of_ocs $α)
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩)
    ← AtomM.run .instances do pure (← eval q(cs_of_ocs $α) c e₁, ← eval q(cs_of_ocs $α) c e₂)
  match ← evalLE sα va vb with
  | .ok p => g.assign q(le_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a ≤ $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to an additive constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is larger\n{g'.mvarId!}"
attribute [local instance] monadLiftOptionMetaM in
def proveLT (g : MVarId) : MetaM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).lt?
    | throwError "ring failed: not of the form `A < B`"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ← synthInstanceQ q(StrictOrderedCommSemiring $α)
  assumeInstancesCommute
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let c ← mkCache q(cs_of_socs $α)
  let (⟨a, va, pa⟩, ⟨b, vb, pb⟩)
    ← AtomM.run .instances do pure (← eval q(cs_of_socs $α) c e₁, ← eval q(cs_of_socs $α) c e₂)
  match ← evalLT sα va vb with
  | .ok p => g.assign q(lt_congr $pa $p $pb)
  | .error e =>
    let g' ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a < $b))
    match e with
    | notComparable =>
      throwError "ring failed, ring expressions not equal up to an additive constant\n{g'.mvarId!}"
    | tooSmall => throwError "comparison failed, LHS is at least as large\n{g'.mvarId!}"
end Mathlib.Tactic.Ring