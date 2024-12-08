import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum.GCD
namespace Tactic
namespace NormNum
open Qq Lean Elab.Tactic Mathlib.Meta.NormNum
theorem int_not_isCoprime_helper (x y : ℤ) (d : ℕ) (hd : Int.gcd x y = d)
    (h : Nat.beq d 1 = false) : ¬ IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one, hd]
  exact Nat.ne_of_beq_eq_false h
theorem isInt_isCoprime : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → IsCoprime nx ny → IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h
theorem isInt_not_isCoprime : {x y nx ny : ℤ} →
    IsInt x nx → IsInt y ny → ¬ IsCoprime nx ny → ¬ IsCoprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h
def proveIntIsCoprime (ex ey : Q(ℤ)) : Q(IsCoprime $ex $ey) ⊕ Q(¬ IsCoprime $ex $ey) :=
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  if ed.natLit! = 1 then
    have pf' : Q(Int.gcd $ex $ey = 1) := pf
    Sum.inl q(Int.isCoprime_iff_gcd_eq_one.mpr $pf')
  else
    have h : Q(Nat.beq $ed 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(int_not_isCoprime_helper $ex $ey $ed $pf $h)
@[norm_num IsCoprime (_ : ℤ) (_ : ℤ)]
def evalIntIsCoprime : NormNumExt where eval {_ _} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  match proveIntIsCoprime ex ey with
  | .inl pf =>
    have pf' : Q(IsCoprime $x $y) := q(isInt_isCoprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ IsCoprime $x $y) := q(isInt_not_isCoprime $p $q $pf)
    return .isFalse pf'
end NormNum
end Tactic