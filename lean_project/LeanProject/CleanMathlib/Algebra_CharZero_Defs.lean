import Mathlib.Data.Int.Cast.Defs
import Mathlib.Logic.Function.Basic
class CharZero (R) [AddMonoidWithOne R] : Prop where
  cast_injective : Function.Injective (Nat.cast : ℕ → R)
variable {R : Type*}
theorem charZero_of_inj_zero [AddGroupWithOne R] (H : ∀ n : ℕ, (n : R) = 0 → n = 0) :
    CharZero R :=
  ⟨@fun m n h => by
    induction m generalizing n with
    | zero => rw [H n]; rw [← h, Nat.cast_zero]
    | succ m ih =>
      cases n
      · apply H; rw [h, Nat.cast_zero]
      · simp only [Nat.cast_succ, add_right_cancel_iff] at h; rwa [ih]⟩
namespace Nat
variable [AddMonoidWithOne R] [CharZero R]
theorem cast_injective : Function.Injective (Nat.cast : ℕ → R) :=
  CharZero.cast_injective
@[simp, norm_cast]
theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
  cast_injective.eq_iff
@[simp, norm_cast]
theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]
@[norm_cast]
theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 :=
  mod_cast n.succ_ne_zero
@[simp, norm_cast]
theorem cast_eq_one {n : ℕ} : (n : R) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]
@[norm_cast]
theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.not
instance (priority := 100) AtLeastTwo.toNeZero (n : ℕ) [n.AtLeastTwo] : NeZero n :=
  ⟨Nat.ne_of_gt (Nat.le_of_lt one_lt)⟩
end Nat
namespace OfNat
variable [AddMonoidWithOne R] [CharZero R]
@[simp] lemma ofNat_ne_zero (n : ℕ) [n.AtLeastTwo] : (no_index (ofNat n) : R) ≠ 0 :=
  Nat.cast_ne_zero.2 (NeZero.ne n)
@[simp] lemma zero_ne_ofNat (n : ℕ) [n.AtLeastTwo] : 0 ≠ (no_index (ofNat n) : R) :=
  (ofNat_ne_zero n).symm
@[simp] lemma ofNat_ne_one (n : ℕ) [n.AtLeastTwo] : (no_index (ofNat n) : R) ≠ 1 :=
  Nat.cast_ne_one.2 (Nat.AtLeastTwo.ne_one)
@[simp] lemma one_ne_ofNat (n : ℕ) [n.AtLeastTwo] : (1 : R) ≠ no_index (ofNat n) :=
  (ofNat_ne_one n).symm
@[simp] lemma ofNat_eq_ofNat {m n : ℕ} [m.AtLeastTwo] [n.AtLeastTwo] :
    (no_index (ofNat m) : R) = no_index (ofNat n) ↔ (ofNat m : ℕ) = ofNat n :=
  Nat.cast_inj
end OfNat
namespace NeZero
instance charZero {M} {n : ℕ} [NeZero n] [AddMonoidWithOne M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr out⟩
instance charZero_one {M} [AddMonoidWithOne M] [CharZero M] : NeZero (1 : M) where
  out := by
    rw [← Nat.cast_one, Nat.cast_ne_zero]
    trivial
instance charZero_ofNat {M} {n : ℕ} [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero M] :
    NeZero (OfNat.ofNat n : M) :=
  ⟨OfNat.ofNat_ne_zero n⟩
end NeZero