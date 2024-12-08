import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.LinearMap.Defs
variable {R : Type*} {M : Type*} [Semiring R]
namespace IsLinearMap
theorem isLinearMap_add [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  · intro x y
    simp [smul_add]
theorem isLinearMap_sub [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp [add_comm, add_assoc, add_left_comm, sub_eq_add_neg]
  · intro x y
    simp [smul_sub]
end IsLinearMap