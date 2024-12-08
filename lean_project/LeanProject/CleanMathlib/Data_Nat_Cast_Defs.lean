import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SplitIfs
variable {R : Type*}
protected def Nat.unaryCast [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1
class Nat.AtLeastTwo (n : ℕ) : Prop where
  prop : n ≥ 2
instance instNatAtLeastTwo {n : ℕ} : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ <| Nat.succ_le_succ <| Nat.zero_le _
namespace Nat.AtLeastTwo
variable {n : ℕ} [n.AtLeastTwo]
lemma one_lt : 1 < n := prop
lemma ne_one : n ≠ 1 := Nat.ne_of_gt one_lt
end Nat.AtLeastTwo
@[nolint unusedArguments]
instance (priority := 100) instOfNatAtLeastTwo {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    OfNat R n where
  ofNat := n.cast
library_note "no_index around OfNat.ofNat"
@[simp, norm_cast] theorem Nat.cast_ofNat {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
  (Nat.cast (no_index (OfNat.ofNat n)) : R) = OfNat.ofNat n := rfl
theorem Nat.cast_eq_ofNat {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    (Nat.cast n : R) = OfNat.ofNat n :=
  rfl
class AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  natCast_zero : natCast 0 = 0 := by intros; rfl
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl
class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R
library_note "coercion into rings"
namespace Nat
variable [AddMonoidWithOne R]
@[simp, norm_cast]
theorem cast_zero : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
@[norm_cast 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _
theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _
@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) :
    ((ite P m n : ℕ) : R) = ite P (m : R) (n : R) := by
  split_ifs <;> rfl
end Nat
namespace Nat
@[simp, norm_cast]
theorem cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by
  rw [cast_succ, Nat.cast_zero, zero_add]
@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_succ, cast_succ, ih, cast_succ, add_assoc]
protected def binCast [Zero R] [One R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0
    then (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2))
    else (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2)) + 1
@[simp]
theorem binCast_eq [AddMonoidWithOne R] (n : ℕ) :
    (Nat.binCast n : R) = ((n : ℕ) : R) := by
  induction n using Nat.strongRecOn with | ind k hk => ?_
  cases k with
  | zero => rw [Nat.binCast, Nat.cast_zero]
  | succ k =>
      rw [Nat.binCast]
      by_cases h : (k + 1) % 2 = 0
      · conv => rhs; rw [← Nat.mod_add_div (k+1) 2]
        rw [if_pos h, hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ← Nat.cast_add]
        rw [h, Nat.zero_add, Nat.succ_mul, Nat.one_mul]
      · conv => rhs; rw [← Nat.mod_add_div (k+1) 2]
        rw [if_neg h, hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ← Nat.cast_add]
        have h1 := Or.resolve_left (Nat.mod_two_eq_zero_or_one (succ k)) h
        rw [h1, Nat.add_comm 1, Nat.succ_mul, Nat.one_mul]
        simp only [Nat.cast_add, Nat.cast_one]
theorem cast_two [AddMonoidWithOne R] : ((2 : ℕ) : R) = (2 : R) := rfl
theorem cast_three [AddMonoidWithOne R] : ((3 : ℕ) : R) = (3 : R) := rfl
theorem cast_four [AddMonoidWithOne R] : ((4 : ℕ) : R) = (4 : R) := rfl
attribute [simp, norm_cast] Int.natAbs_ofNat
end Nat
protected abbrev AddMonoidWithOne.unary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with }
protected abbrev AddMonoidWithOne.binary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast,
    natCast_zero := by simp only [Nat.binCast, Nat.cast],
    natCast_succ := fun n => by
      dsimp only [NatCast.natCast]
      letI : AddMonoidWithOne R := AddMonoidWithOne.unary
      rw [Nat.binCast_eq, Nat.binCast_eq, Nat.cast_succ] }
theorem one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2 : R) := by
  rw [← Nat.cast_one, ← Nat.cast_add]
  apply congrArg
  decide
theorem two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 = (3 : R) := by
  rw [← one_add_one_eq_two, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
  apply congrArg
  decide
theorem three_add_one_eq_four [AddMonoidWithOne R] : 3 + 1 = (4 : R) := by
  rw [← two_add_one_eq_three, ← one_add_one_eq_two, ← Nat.cast_one,
    ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  apply congrArg
  decide
theorem two_add_two_eq_four [AddMonoidWithOne R] : 2 + 2 = (4 : R) := by
  simp [← one_add_one_eq_two, ← Nat.cast_one, ← three_add_one_eq_four,
    ← two_add_one_eq_three, add_assoc]
section nsmul
@[simp] lemma nsmul_one {A} [AddMonoidWithOne A] : ∀ n : ℕ, n • (1 : A) = n
  | 0 => by simp [zero_nsmul]
  | n + 1 => by simp [succ_nsmul, nsmul_one n]
end nsmul