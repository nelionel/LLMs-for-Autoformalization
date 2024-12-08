import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Order.UpperLower.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Cast.Order.Basic
open Set
namespace Nat
@[simp]
theorem range_cast_int : range ((↑) : ℕ → ℤ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 Int.ofNat_nonneg) CanLift.prf
theorem image_cast_int_Icc (a b : ℕ) : (↑) '' Icc a b = Icc (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Icc (by simp [ordConnected_Ici]) a b
theorem image_cast_int_Ico (a b : ℕ) : (↑) '' Ico a b = Ico (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ico (by simp [ordConnected_Ici]) a b
theorem image_cast_int_Ioc (a b : ℕ) : (↑) '' Ioc a b = Ioc (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ioc (by simp [ordConnected_Ici]) a b
theorem image_cast_int_Ioo (a b : ℕ) : (↑) '' Ioo a b = Ioo (a : ℤ) b :=
  (castOrderEmbedding (α := ℤ)).image_Ioo (by simp [ordConnected_Ici]) a b
theorem image_cast_int_Iic (a : ℕ) : (↑) '' Iic a = Icc (0 : ℤ) a := by
  rw [← Icc_bot, image_cast_int_Icc]; rfl
theorem image_cast_int_Iio (a : ℕ) : (↑) '' Iio a = Ico (0 : ℤ) a := by
  rw [← Ico_bot, image_cast_int_Ico]; rfl
theorem image_cast_int_Ici (a : ℕ) : (↑) '' Ici a = Ici (a : ℤ) :=
  (castOrderEmbedding (α := ℤ)).image_Ici (by simp [isUpperSet_Ici]) a
theorem image_cast_int_Ioi (a : ℕ) : (↑) '' Ioi a = Ioi (a : ℤ) :=
  (castOrderEmbedding (α := ℤ)).image_Ioi (by simp [isUpperSet_Ici]) a
end Nat