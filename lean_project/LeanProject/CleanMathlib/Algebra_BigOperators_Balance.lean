import Mathlib.Algebra.BigOperators.Expect
open Finset Function
open scoped BigOperators
variable {ι H F G : Type*}
namespace Fintype
section AddCommGroup
variable [Fintype ι] [AddCommGroup G] [Module ℚ≥0 G] [AddCommGroup H] [Module ℚ≥0 H]
def balance (f : ι → G) : ι → G := f - Function.const _ (𝔼 y, f y)
lemma balance_apply (f : ι → G) (x : ι) : balance f x = f x - 𝔼 y, f y := rfl
@[simp] lemma balance_zero : balance (0 : ι → G) = 0 := by simp [balance]
@[simp] lemma balance_add (f g : ι → G) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]
@[simp] lemma balance_sub (f g : ι → G) : balance (f - g) = balance f - balance g := by
  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]
@[simp] lemma balance_neg (f : ι → G) : balance (-f) = -balance f := by
  simp only [balance, expect_neg_distrib, const_neg, neg_sub', Pi.neg_apply]
@[simp] lemma sum_balance (f : ι → G) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply]
@[simp] lemma expect_balance (f : ι → G) : 𝔼 x, balance f x = 0 := by simp [expect]
@[simp] lemma balance_idem (f : ι → G) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]
@[simp] lemma map_balance [FunLike F G H] [LinearMapClass F ℚ≥0 G H] (g : F) (f : ι → G) (a : ι) :
    g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]
end AddCommGroup
end Fintype