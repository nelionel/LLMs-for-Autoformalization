import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Localization.Defs
import Mathlib.SetTheory.Game.Birthday
import Mathlib.SetTheory.Surreal.Multiplication
import Mathlib.Tactic.Linarith
universe u
namespace SetTheory
namespace PGame
def powHalf : ℕ → PGame
  | 0 => 1
  | n + 1 => ⟨PUnit, PUnit, 0, fun _ => powHalf n⟩
@[simp]
theorem powHalf_zero : powHalf 0 = 1 :=
  rfl
theorem powHalf_leftMoves (n) : (powHalf n).LeftMoves = PUnit := by cases n <;> rfl
theorem powHalf_zero_rightMoves : (powHalf 0).RightMoves = PEmpty :=
  rfl
theorem powHalf_succ_rightMoves (n) : (powHalf (n + 1)).RightMoves = PUnit :=
  rfl
@[simp]
theorem powHalf_moveLeft (n i) : (powHalf n).moveLeft i = 0 := by cases n <;> cases i <;> rfl
@[simp]
theorem powHalf_succ_moveRight (n i) : (powHalf (n + 1)).moveRight i = powHalf n :=
  rfl
instance uniquePowHalfLeftMoves (n) : Unique (powHalf n).LeftMoves := by
  cases n <;> exact PUnit.unique
instance isEmpty_powHalf_zero_rightMoves : IsEmpty (powHalf 0).RightMoves :=
  inferInstanceAs (IsEmpty PEmpty)
instance uniquePowHalfSuccRightMoves (n) : Unique (powHalf (n + 1)).RightMoves :=
  PUnit.unique
@[simp]
theorem birthday_half : birthday (powHalf 1) = 2 := by
  rw [birthday_def]; simp
theorem numeric_powHalf (n) : (powHalf n).Numeric := by
  induction n with
  | zero => exact numeric_one
  | succ n hn =>
    constructor
    · simpa using hn.moveLeft_lt default
    · exact ⟨fun _ => numeric_zero, fun _ => hn⟩
theorem powHalf_succ_lt_powHalf (n : ℕ) : powHalf (n + 1) < powHalf n :=
  (numeric_powHalf (n + 1)).lt_moveRight default
theorem powHalf_succ_le_powHalf (n : ℕ) : powHalf (n + 1) ≤ powHalf n :=
  (powHalf_succ_lt_powHalf n).le
theorem powHalf_le_one (n : ℕ) : powHalf n ≤ 1 := by
  induction n with
  | zero => exact le_rfl
  | succ n hn => exact (powHalf_succ_le_powHalf n).trans hn
theorem powHalf_succ_lt_one (n : ℕ) : powHalf (n + 1) < 1 :=
  (powHalf_succ_lt_powHalf n).trans_le <| powHalf_le_one n
theorem powHalf_pos (n : ℕ) : 0 < powHalf n := by
  rw [← lf_iff_lt numeric_zero (numeric_powHalf n), zero_lf_le]; simp
theorem zero_le_powHalf (n : ℕ) : 0 ≤ powHalf n :=
  (powHalf_pos n).le
theorem add_powHalf_succ_self_eq_powHalf (n) : powHalf (n + 1) + powHalf (n + 1) ≈ powHalf n := by
  induction' n using Nat.strong_induction_on with n hn
  constructor <;> rw [le_iff_forall_lf] <;> constructor
  · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> apply lf_of_lt
    · calc
        0 + powHalf n.succ ≈ powHalf n.succ := zero_add_equiv _
        _ < powHalf n := powHalf_succ_lt_powHalf n
    · calc
        powHalf n.succ + 0 ≈ powHalf n.succ := add_zero_equiv _
        _ < powHalf n := powHalf_succ_lt_powHalf n
  · cases' n with n
    · rintro ⟨⟩
    rintro ⟨⟩
    apply lf_of_moveRight_le
    swap
    · exact Sum.inl default
    calc
      powHalf n.succ + powHalf (n.succ + 1) ≤ powHalf n.succ + powHalf n.succ :=
        add_le_add_left (powHalf_succ_le_powHalf _) _
      _ ≈ powHalf n := hn _ (Nat.lt_succ_self n)
  · simp only [powHalf_moveLeft, forall_const]
    apply lf_of_lt
    calc
      0 ≈ 0 + 0 := Equiv.symm (add_zero_equiv 0)
      _ ≤ powHalf n.succ + 0 := add_le_add_right (zero_le_powHalf _) _
      _ < powHalf n.succ + powHalf n.succ := add_lt_add_left (powHalf_pos _) _
  · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> apply lf_of_lt
    · calc
        powHalf n ≈ powHalf n + 0 := Equiv.symm (add_zero_equiv _)
        _ < powHalf n + powHalf n.succ := add_lt_add_left (powHalf_pos _) _
    · calc
        powHalf n ≈ 0 + powHalf n := Equiv.symm (zero_add_equiv _)
        _ < powHalf n.succ + powHalf n := add_lt_add_right (powHalf_pos _) _
theorem half_add_half_equiv_one : powHalf 1 + powHalf 1 ≈ 1 :=
  add_powHalf_succ_self_eq_powHalf 0
end PGame
end SetTheory
namespace Surreal
open SetTheory PGame
def powHalf (n : ℕ) : Surreal :=
  ⟦⟨PGame.powHalf n, PGame.numeric_powHalf n⟩⟧
@[simp]
theorem powHalf_zero : powHalf 0 = 1 :=
  rfl
@[simp]
theorem double_powHalf_succ_eq_powHalf (n : ℕ) : 2 * powHalf (n + 1) = powHalf n := by
  rw [two_mul]; exact Quotient.sound (PGame.add_powHalf_succ_self_eq_powHalf n)
@[simp]
theorem nsmul_pow_two_powHalf (n : ℕ) : 2 ^ n * powHalf n = 1 := by
  induction' n with n hn
  · simp only [pow_zero, powHalf_zero, mul_one]
  · rw [← hn, ← double_powHalf_succ_eq_powHalf n, ← mul_assoc (2 ^ n) 2 (powHalf (n + 1)),
      pow_succ', mul_comm 2 (2 ^ n)]
@[simp]
theorem nsmul_pow_two_powHalf' (n k : ℕ) : 2 ^ n * powHalf (n + k) = powHalf k := by
  induction' k with k hk
  · simp only [add_zero, Surreal.nsmul_pow_two_powHalf, eq_self_iff_true,
      Surreal.powHalf_zero]
  · rw [← double_powHalf_succ_eq_powHalf (n + k), ← double_powHalf_succ_eq_powHalf k,
      ← mul_assoc, mul_comm (2 ^ n) 2, mul_assoc] at hk
    rw [← zsmul_eq_zsmul_iff' two_ne_zero]
    simpa only [zsmul_eq_mul, Int.cast_ofNat]
theorem zsmul_pow_two_powHalf (m : ℤ) (n k : ℕ) :
    (m * 2 ^ n) * powHalf (n + k) = m * powHalf k := by
  rw [mul_assoc]
  congr
  exact nsmul_pow_two_powHalf' n k
theorem dyadic_aux {m₁ m₂ : ℤ} {y₁ y₂ : ℕ} (h₂ : m₁ * 2 ^ y₁ = m₂ * 2 ^ y₂) :
    m₁ * powHalf y₂ = m₂ * powHalf y₁ := by
  revert m₁ m₂
  wlog h : y₁ ≤ y₂
  · intro m₁ m₂ aux; exact (this (le_of_not_le h) aux.symm).symm
  intro m₁ m₂ h₂
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h
  rw [add_comm, pow_add, ← mul_assoc, mul_eq_mul_right_iff] at h₂
  cases' h₂ with h₂ h₂
  · rw [h₂, add_comm]
    simp_rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, zsmul_pow_two_powHalf m₂ c y₁]
  · have := Nat.one_le_pow y₁ 2 Nat.succ_pos'
    norm_cast at h₂; omega
noncomputable def dyadicMap : Localization.Away (2 : ℤ) →+ Surreal where
  toFun x :=
    (Localization.liftOn x fun x y => x * powHalf (Submonoid.log y)) <| by
      intro m₁ m₂ n₁ n₂ h₁
      obtain ⟨⟨n₃, y₃, hn₃⟩, h₂⟩ := Localization.r_iff_exists.mp h₁
      simp only [Subtype.coe_mk, mul_eq_mul_left_iff] at h₂
      cases h₂
      · obtain ⟨a₁, ha₁⟩ := n₁.prop
        obtain ⟨a₂, ha₂⟩ := n₂.prop
        simp only at ha₁ ha₂ ⊢
        have hn₁ : n₁ = Submonoid.pow 2 a₁ := Subtype.ext ha₁.symm
        have hn₂ : n₂ = Submonoid.pow 2 a₂ := Subtype.ext ha₂.symm
        have h₂ : 1 < (2 : ℤ).natAbs := one_lt_two
        rw [hn₁, hn₂, Submonoid.log_pow_int_eq_self h₂, Submonoid.log_pow_int_eq_self h₂]
        apply dyadic_aux
        rwa [ha₁, ha₂, mul_comm, mul_comm m₂]
      · have : (1 : ℤ) ≤ 2 ^ y₃ := mod_cast Nat.one_le_pow y₃ 2 Nat.succ_pos'
        linarith
  map_zero' := by simp_rw [Localization.liftOn_zero _ _, Int.cast_zero, zero_mul]
  map_add' x y :=
    Localization.induction_on₂ x y <| by
      rintro ⟨a, ⟨b, ⟨b', rfl⟩⟩⟩ ⟨c, ⟨d, ⟨d', rfl⟩⟩⟩
      have h₂ : 1 < (2 : ℤ).natAbs := one_lt_two
      have hpow₂ := Submonoid.log_pow_int_eq_self h₂
      simp_rw [Submonoid.pow_apply] at hpow₂
      simp_rw [Localization.add_mk, Localization.liftOn_mk,
        Submonoid.log_mul (Int.pow_right_injective h₂), hpow₂]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      calc
        (2 ^ b' * c + 2 ^ d' * a) * powHalf (b' + d') =
            (c * 2 ^ b') * powHalf (b' + d') + (a * 2 ^ d') * powHalf (d' + b') := by
          simp only [right_distrib, mul_comm, add_comm]
        _ = c * powHalf d' + a * powHalf b' := by simp only [zsmul_pow_two_powHalf]
        _ = a * powHalf b' + c * powHalf d' := add_comm _ _
@[simp]
theorem dyadicMap_apply (m : ℤ) (p : Submonoid.powers (2 : ℤ)) :
    dyadicMap (IsLocalization.mk' (Localization (Submonoid.powers 2)) m p) =
      m * powHalf (Submonoid.log p) := by
  rw [← Localization.mk_eq_mk']; rfl
theorem dyadicMap_apply_pow (m : ℤ) (n : ℕ) :
    dyadicMap (IsLocalization.mk' (Localization (Submonoid.powers 2)) m (Submonoid.pow 2 n)) =
      m • powHalf n := by
  rw [dyadicMap_apply, @Submonoid.log_pow_int_eq_self 2 one_lt_two]
  simp only [zsmul_eq_mul]
@[simp]
theorem dyadicMap_apply_pow' (m : ℤ) (n : ℕ) :
    m * Surreal.powHalf (Submonoid.log (Submonoid.pow (2 : ℤ) n)) = m * powHalf n := by
  rw [@Submonoid.log_pow_int_eq_self 2 one_lt_two]
def dyadic : Set Surreal :=
  Set.range dyadicMap
end Surreal