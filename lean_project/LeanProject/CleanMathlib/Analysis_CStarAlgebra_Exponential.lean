import Mathlib.Analysis.Normed.Algebra.Exponential
open NormedSpace 
section Star
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
open Complex
@[simps]
noncomputable def selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A :=
  ⟨exp ℂ ((I • a.val) : A),
      exp_mem_unitary_of_mem_skewAdjoint _ (a.prop.smul_mem_skewAdjoint conj_I)⟩
open selfAdjoint
theorem Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    expUnitary (a + b) = expUnitary a * expUnitary b := by
  ext
  have hcomm : Commute (I • (a : A)) (I • (b : A)) := by
    unfold Commute SemiconjBy
    simp only [h.eq, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  simpa only [expUnitary_coe, AddSubgroup.coe_add, smul_add] using exp_add_of_commute hcomm
theorem Commute.expUnitary {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    Commute (expUnitary a) (expUnitary b) :=
  calc
    selfAdjoint.expUnitary a * selfAdjoint.expUnitary b =
        selfAdjoint.expUnitary b * selfAdjoint.expUnitary a := by
      rw [← h.expUnitary_add, ← h.symm.expUnitary_add, add_comm]
end Star