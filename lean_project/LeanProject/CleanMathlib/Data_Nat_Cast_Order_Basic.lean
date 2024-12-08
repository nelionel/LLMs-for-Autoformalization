import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.Nat.Cast.NeZero
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Order.Hom.Basic
assert_not_exists OrderedCommMonoid
variable {α : Type*}
namespace Nat
section OrderedSemiring
variable [AddMonoidWithOne α] [PartialOrder α]
variable [AddLeftMono α] [ZeroLEOneClass α]
@[mono]
theorem mono_cast : Monotone (Nat.cast : ℕ → α) :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one
@[deprecated mono_cast (since := "2024-02-10")]
theorem cast_le_cast {a b : ℕ} (h : a ≤ b) : (a : α) ≤ b := mono_cast h
@[gcongr]
theorem _root_.GCongr.natCast_le_natCast {a b : ℕ} (h : a ≤ b) : (a : α) ≤ b := mono_cast h
@[simp low]
theorem cast_nonneg' (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)
@[simp low]
theorem ofNat_nonneg' (n : ℕ) [n.AtLeastTwo] : 0 ≤ (no_index (OfNat.ofNat n : α)) := cast_nonneg' n
section Nontrivial
variable [NeZero (1 : α)]
theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 := by
  apply zero_lt_one.trans_le
  convert (@mono_cast α _).imp (?_ : 1 ≤ n + 1)
  <;> simp
@[simp low]
theorem cast_pos' {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]
end Nontrivial
variable [CharZero α] {m n : ℕ}
theorem strictMono_cast : StrictMono (Nat.cast : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective
@[gcongr]
lemma _root_.GCongr.natCast_lt_natCast {a b : ℕ} (h : a < b) : (a : α) < b := strictMono_cast h
@[simps! (config := .asFn)]
def castOrderEmbedding : ℕ ↪o α :=
  OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast
@[simp, norm_cast]
theorem cast_le : (m : α) ≤ n ↔ m ≤ n :=
  strictMono_cast.le_iff_le
@[simp, norm_cast, mono]
theorem cast_lt : (m : α) < n ↔ m < n :=
  strictMono_cast.lt_iff_lt
@[simp, norm_cast]
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]
@[simp, norm_cast]
theorem one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]
@[simp, norm_cast]
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, Nat.lt_succ_iff, le_zero]
@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]
@[simp] lemma cast_nonpos : (n : α) ≤ 0 ↔ n = 0 := by norm_cast; omega
section
variable [m.AtLeastTwo]
@[simp]
theorem ofNat_le_cast : (no_index (OfNat.ofNat m : α)) ≤ n ↔ (OfNat.ofNat m : ℕ) ≤ n :=
  cast_le
@[simp]
theorem ofNat_lt_cast : (no_index (OfNat.ofNat m : α)) < n ↔ (OfNat.ofNat m : ℕ) < n :=
  cast_lt
end
variable [n.AtLeastTwo]
@[simp]
theorem cast_le_ofNat : (m : α) ≤ (no_index (OfNat.ofNat n)) ↔ m ≤ OfNat.ofNat n :=
  cast_le
@[simp]
theorem cast_lt_ofNat : (m : α) < (no_index (OfNat.ofNat n)) ↔ m < OfNat.ofNat n :=
  cast_lt
@[simp]
theorem one_lt_ofNat : 1 < (no_index (OfNat.ofNat n : α)) :=
  one_lt_cast.mpr AtLeastTwo.one_lt
@[simp]
theorem one_le_ofNat : 1 ≤ (no_index (OfNat.ofNat n : α)) :=
  one_le_cast.mpr NeZero.one_le
@[simp]
theorem not_ofNat_le_one : ¬(no_index (OfNat.ofNat n : α)) ≤ 1 :=
  (cast_le_one.not.trans not_le).mpr AtLeastTwo.one_lt
@[simp]
theorem not_ofNat_lt_one : ¬(no_index (OfNat.ofNat n : α)) < 1 :=
  mt le_of_lt not_ofNat_le_one
variable [m.AtLeastTwo]
theorem ofNat_le :
    (no_index (OfNat.ofNat m : α)) ≤ (no_index (OfNat.ofNat n)) ↔
      (OfNat.ofNat m : ℕ) ≤ OfNat.ofNat n :=
  cast_le
theorem ofNat_lt :
    (no_index (OfNat.ofNat m : α)) < (no_index (OfNat.ofNat n)) ↔
      (OfNat.ofNat m : ℕ) < OfNat.ofNat n :=
  cast_lt
end OrderedSemiring
end Nat
instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α where exists_pair_ne :=
  ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩
section RingHomClass
variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]
theorem NeZero.nat_of_injective {n : ℕ} [NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h ↦ NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero f]⟩
end RingHomClass