import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Module.OrderedSMul
section OrderedAlgebra
variable {R A : Type*} [OrderedCommRing R] [OrderedRing A] [Algebra R A] [OrderedSMul R A]
theorem algebraMap_monotone : Monotone (algebraMap R A) := fun a b h => by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← sub_nonneg, ← sub_smul]
  trans (b - a) • (0 : A)
  · simp
  · exact smul_le_smul_of_nonneg_left zero_le_one (sub_nonneg.mpr h)
end OrderedAlgebra