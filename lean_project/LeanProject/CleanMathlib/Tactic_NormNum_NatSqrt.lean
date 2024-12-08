import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.NormNum
namespace Tactic
namespace NormNum
open Qq Lean Elab.Tactic Mathlib.Meta.NormNum
lemma nat_sqrt_helper {x y r : ℕ} (hr : y * y + r = x) (hle : Nat.ble r (2 * y)) :
    Nat.sqrt x = y := by
  rw [← hr, ← pow_two]
  rw [two_mul] at hle
  exact Nat.sqrt_add_eq' _ (Nat.le_of_ble_eq_true hle)
theorem isNat_sqrt : {x nx z : ℕ} → IsNat x nx → Nat.sqrt nx = z → IsNat (Nat.sqrt x) z
  | _, _, _, ⟨rfl⟩, rfl => ⟨rfl⟩
def proveNatSqrt (ex : Q(ℕ)) : (ey : Q(ℕ)) × Q(Nat.sqrt $ex = $ey) :=
  match ex.natLit! with
  | 0 => show (ey : Q(ℕ)) × Q(Nat.sqrt 0 = $ey) from ⟨mkRawNatLit 0, q(Nat.sqrt_zero)⟩
  | 1 => show (ey : Q(ℕ)) × Q(Nat.sqrt 1 = $ey) from ⟨mkRawNatLit 1, q(Nat.sqrt_one)⟩
  | x =>
    let y := Nat.sqrt x
    have ey : Q(ℕ) := mkRawNatLit y
    have er : Q(ℕ) := mkRawNatLit (x - y * y)
    have hr : Q($ey * $ey + $er = $ex) := (q(Eq.refl $ex) : Expr)
    have hle : Q(Nat.ble $er (2 * $ey)) := (q(Eq.refl true) : Expr)
    ⟨ey, q(nat_sqrt_helper $hr $hle)⟩
@[norm_num Nat.sqrt _]
def evalNatSqrt : NormNumExt where eval {_ _} e := do
  let .app _ (x : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, pf⟩ := proveNatSqrt ex
  let pf' : Q(IsNat (Nat.sqrt $x) $ey) := q(isNat_sqrt $p $pf)
  return .isNat sℕ ey pf'
end NormNum
end Tactic