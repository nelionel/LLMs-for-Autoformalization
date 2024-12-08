import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.ENNReal
open Set Function
variable {α : Type*} (s : Set α)
namespace ENNReal
@[simp]
lemma tsum_set_one_eq : ∑' (_ : s), (1 : ℝ≥0∞) = s.encard := by
  obtain (hfin | hinf) := Set.finite_or_infinite s
  · lift s to Finset α using hfin
    simp [tsum_fintype]
  · have : Infinite s := infinite_coe_iff.mpr hinf
    rw [tsum_const_eq_top_of_ne_zero one_ne_zero, encard_eq_top hinf, ENat.toENNReal_top]
@[simp]
lemma tsum_set_const_eq (c : ℝ≥0∞) : ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
  nth_rw 1 [← one_mul c]
  rw [ENNReal.tsum_mul_right,tsum_set_one_eq]
end ENNReal