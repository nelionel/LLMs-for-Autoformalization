import Mathlib.Algebra.Periodic
import Mathlib.Topology.ContinuousMap.Algebra
assert_not_exists StoneCech
assert_not_exists StarModule
namespace ContinuousMap
section Periodicity
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
theorem periodic_tsum_comp_add_zsmul [AddCommGroup X] [TopologicalAddGroup X] [AddCommMonoid Y]
    [ContinuousAdd Y] [T2Space Y] (f : C(X, Y)) (p : X) :
    Function.Periodic (⇑(∑' n : ℤ, f.comp (ContinuousMap.addRight (n • p)))) p := by
  intro x
  by_cases h : Summable fun n : ℤ => f.comp (ContinuousMap.addRight (n • p))
  · convert congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : ℤ)).tsum_eq _) using 1
    simp_rw [← tsum_apply h]
    erw [← tsum_apply ((Equiv.addRight (1 : ℤ)).summable_iff.mpr h)]
    simp [coe_addRight, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]
end Periodicity
end ContinuousMap