import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Ring.Pointwise.Set
open scoped Pointwise
namespace Finset
variable {α β : Type*}
protected def distribNeg [DecidableEq α] [Mul α] [HasDistribNeg α] : HasDistribNeg (Finset α) :=
  coe_injective.hasDistribNeg _ coe_neg coe_mul
scoped[Pointwise] attribute [instance] Finset.distribNeg
section Distrib
variable [DecidableEq α] [Distrib α] (s t u : Finset α)
lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image₂_distrib_subset_left mul_add
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image₂_distrib_subset_right add_mul
end Distrib
section Ring
variable [Ring α] [AddCommGroup β] [Module α β] [DecidableEq β] {s : Finset α} {t : Finset β}
  {a : α}
@[simp]
lemma neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, image_image, neg_smul, Function.comp_def]
@[simp]
protected lemma neg_smul [DecidableEq α] : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image₂_image_left_comm neg_smul
end Ring
end Finset