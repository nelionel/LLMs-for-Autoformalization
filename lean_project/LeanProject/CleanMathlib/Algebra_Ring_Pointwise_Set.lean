import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Ring.Defs
assert_not_exists OrderedAddCommMonoid
open Function
open scoped Pointwise
variable {α : Type*}
namespace Set
protected noncomputable def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) where
  __ := Set.involutiveNeg
  neg_mul _ _ := by simp_rw [← image_neg_eq_neg]; exact image2_image_left_comm neg_mul
  mul_neg _ _ := by simp_rw [← image_neg_eq_neg]; exact image_image2_right_comm mul_neg
scoped[Pointwise] attribute [instance] Set.hasDistribNeg
section Distrib
variable [Distrib α] (s t u : Set α)
lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u := image2_distrib_subset_left mul_add
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u := image2_distrib_subset_right add_mul
end Distrib
end Set