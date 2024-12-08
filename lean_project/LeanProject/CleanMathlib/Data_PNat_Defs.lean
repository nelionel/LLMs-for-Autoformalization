import Mathlib.Data.Nat.Defs
import Mathlib.Data.PNat.Notation
import Mathlib.Order.Basic
import Mathlib.Tactic.Coe
import Mathlib.Tactic.Lift
import Mathlib.Data.Int.Order.Basic
deriving instance LinearOrder for PNat
instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩
instance (n : ℕ) [NeZero n] : OfNat ℕ+ n :=
  ⟨⟨n, Nat.pos_of_ne_zero <| NeZero.ne n⟩⟩
namespace PNat
@[simp]
theorem mk_coe (n h) : (PNat.val (⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl
def natPred (i : ℕ+) : ℕ :=
  i - 1
@[simp]
theorem natPred_eq_pred {n : ℕ} (h : 0 < n) : natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl
end PNat
namespace Nat
def toPNat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩
def succPNat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩
@[simp]
theorem succPNat_coe (n : ℕ) : (succPNat n : ℕ) = succ n :=
  rfl
@[simp]
theorem natPred_succPNat (n : ℕ) : n.succPNat.natPred = n :=
  rfl
@[simp]
theorem _root_.PNat.succPNat_natPred (n : ℕ+) : n.natPred.succPNat = n :=
  Subtype.eq <| succ_pred_eq_of_pos n.2
def toPNat' (n : ℕ) : ℕ+ :=
  succPNat (pred n)
@[simp]
theorem toPNat'_zero : Nat.toPNat' 0 = 1 := rfl
@[simp]
theorem toPNat'_coe : ∀ n : ℕ, (toPNat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    rfl
end Nat
namespace PNat
open Nat
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k :=
  Iff.rfl
theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl
@[simp, norm_cast]
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl
@[simp]
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2
theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.eq
theorem coe_injective : Function.Injective PNat.val :=
  Subtype.coe_injective
@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'
instance _root_.NeZero.pnat {a : ℕ+} : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩
theorem toPNat'_coe {n : ℕ} : 0 < n → (n.toPNat' : ℕ) = n :=
  succ_pred_eq_of_pos
@[simp]
theorem coe_toPNat' (n : ℕ+) : (n : ℕ).toPNat' = n :=
  eq (toPNat'_coe n.pos)
@[simp]
theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2
@[simp]
theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  not_lt_of_le n.one_le
instance : Inhabited ℕ+ :=
  ⟨1⟩
@[simp]
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl
@[norm_cast]
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl
@[simp, norm_cast]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  Subtype.coe_injective.eq_iff' one_coe
instance : WellFoundedRelation ℕ+ :=
  measure (fun (a : ℕ+) => (a : ℕ))
def strongInductionOn {p : ℕ+ → Sort*} (n : ℕ+) : (∀ k, (∀ m, m < k → p m) → p k) → p n
  | IH => IH _ fun a _ => strongInductionOn a IH
termination_by n.1
def modDivAux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
  | k, 0, q => ⟨k, q.pred⟩
  | _, r + 1, q => ⟨⟨r + 1, Nat.succ_pos r⟩, q⟩
def modDiv (m k : ℕ+) : ℕ+ × ℕ :=
  modDivAux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2
theorem mod_coe (m k : ℕ+) :
    (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) := by
  dsimp [mod, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl
theorem div_coe (m k : ℕ+) :
    (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) := by
  dsimp [div, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩
end PNat
section CanLift
instance Nat.canLiftPNat : CanLift ℕ ℕ+ (↑) (fun n => 0 < n) :=
  ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩
instance Int.canLiftPNat : CanLift ℤ ℕ+ (↑) ((0 < ·)) :=
  ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe, if_pos (Int.natAbs_pos.2 hn.ne'),
        Int.natAbs_of_nonneg hn.le]⟩⟩
end CanLift