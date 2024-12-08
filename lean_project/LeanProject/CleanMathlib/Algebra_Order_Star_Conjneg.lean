import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Star.Conjneg
open scoped ComplexConjugate
variable {G R : Type*} [AddGroup G]
section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f : G → R}
@[simp] lemma conjneg_nonneg : 0 ≤ conjneg f ↔ 0 ≤ f :=
  (Equiv.neg _).forall_congr' <| by simp [starRingEnd_apply]
@[simp] lemma conjneg_pos : 0 < conjneg f ↔ 0 < f := by
  simp_rw [lt_iff_le_and_ne, ne_comm, conjneg_nonneg, conjneg_ne_zero]
end OrderedCommSemiring
section OrderedCommRing
variable [OrderedCommRing R] [StarRing R] [StarOrderedRing R] {f : G → R}
@[simp] lemma conjneg_nonpos : conjneg f ≤ 0 ↔ f ≤ 0 := by
  simp_rw [← neg_nonneg, ← conjneg_neg, conjneg_nonneg]
@[simp] lemma conjneg_neg' : conjneg f < 0 ↔ f < 0 := by
  simp_rw [← neg_pos, ← conjneg_neg, conjneg_pos]
end OrderedCommRing