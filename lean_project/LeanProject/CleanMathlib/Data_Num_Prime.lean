import Mathlib.Data.Num.Lemmas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring
namespace PosNum
def minFacAux (n : PosNum) : ℕ → PosNum → PosNum
  | 0, _ => n
  | fuel + 1, k =>
    if n < k.bit1 * k.bit1 then n else if k.bit1 ∣ n then k.bit1 else minFacAux n fuel k.succ
theorem minFacAux_to_nat {fuel : ℕ} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bit1) :
    (minFacAux n fuel k : ℕ) = Nat.minFacAux n k.bit1 := by
  induction' fuel with fuel ih generalizing k <;> rw [minFacAux, Nat.minFacAux]
  · rw [Nat.zero_add, Nat.sqrt_lt] at h
    simp only [h, ite_true]
  simp_rw [← mul_to_nat]
  simp only [cast_lt, dvd_to_nat]
  split_ifs <;> try rfl
  rw [ih] <;> [congr; convert Nat.lt_succ_of_lt h using 1] <;>
    simp only [cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
      add_left_comm, ← one_add_one_eq_two]
def minFac : PosNum → PosNum
  | 1 => 1
  | bit0 _ => 2
  | bit1 n => minFacAux (bit1 n) n 1
@[simp]
theorem minFac_to_nat (n : PosNum) : (minFac n : ℕ) = Nat.minFac n := by
  cases' n with n
  · rfl
  · rw [minFac, Nat.minFac_eq, if_neg]
    swap
    · simp [← two_mul]
    rw [minFacAux_to_nat]
    · rfl
    simp only [cast_one, cast_bit1]
    rw [Nat.sqrt_lt]
    calc
      (n : ℕ) + (n : ℕ) + 1 ≤ (n : ℕ) + (n : ℕ) + (n : ℕ) := by simp
      _ = (n : ℕ) * (1 + 1 + 1) := by simp only [mul_add, mul_one]
      _ < _ := by
        set_option simprocs false in simp [mul_lt_mul]
  · rw [minFac, Nat.minFac_eq, if_pos]
    · rfl
    simp [← two_mul]
@[simp]
def Prime (n : PosNum) : Prop :=
  Nat.Prime n
instance decidablePrime : DecidablePred PosNum.Prime
  | 1 => Decidable.isFalse Nat.not_prime_one
  | bit0 n =>
    decidable_of_iff' (n = 1)
      (by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans <| eq_comm.trans ?_)
        · exact add_le_add (Nat.succ_le_of_lt (to_nat_pos _)) (Nat.succ_le_of_lt (to_nat_pos _))
        rw [← minFac_to_nat, to_nat_inj]
        exact ⟨bit0.inj, congr_arg _⟩)
  | bit1 n =>
    decidable_of_iff' (minFacAux (bit1 n) n 1 = bit1 n) <| by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans ?_)
        · simp only [cast_bit1]
          have := to_nat_pos n
          omega
        rw [← minFac_to_nat, to_nat_inj]; rfl
end PosNum
namespace Num
def minFac : Num → PosNum
  | 0 => 2
  | pos n => n.minFac
@[simp]
theorem minFac_to_nat : ∀ n : Num, (minFac n : ℕ) = Nat.minFac n
  | 0 => rfl
  | pos _ => PosNum.minFac_to_nat _
@[simp]
def Prime (n : Num) : Prop :=
  Nat.Prime n
instance decidablePrime : DecidablePred Num.Prime
  | 0 => Decidable.isFalse Nat.not_prime_zero
  | pos n => PosNum.decidablePrime n
end Num