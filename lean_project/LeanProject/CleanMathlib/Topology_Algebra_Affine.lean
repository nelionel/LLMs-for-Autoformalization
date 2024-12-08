import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
namespace AffineMap
variable {R E F : Type*}
variable [AddCommGroup E] [TopologicalSpace E]
variable [AddCommGroup F] [TopologicalSpace F] [TopologicalAddGroup F]
section Ring
variable [Ring R] [Module R E] [Module R F]
theorem continuous_iff {f : E →ᵃ[R] F} : Continuous f ↔ Continuous f.linear := by
  constructor
  · intro hc
    rw [decomp' f]
    exact hc.sub continuous_const
  · intro hc
    rw [decomp f]
    exact hc.add continuous_const
@[continuity]
theorem lineMap_continuous [TopologicalSpace R] [ContinuousSMul R F] {p v : F} :
    Continuous (lineMap p v : R →ᵃ[R] F) :=
  continuous_iff.mpr <|
    (continuous_id.smul continuous_const).add <| @continuous_const _ _ _ _ (0 : F)
end Ring
section CommRing
variable [CommRing R] [Module R F] [ContinuousConstSMul R F]
@[continuity]
theorem homothety_continuous (x : F) (t : R) : Continuous <| homothety x t := by
  suffices ⇑(homothety x t) = fun y => t • (y - x) + x by
    rw [this]
    exact ((continuous_id.sub continuous_const).const_smul _).add continuous_const
  ext y
  simp [homothety_apply]
end CommRing
section Field
variable [Field R] [Module R F] [ContinuousConstSMul R F]
theorem homothety_isOpenMap (x : F) (t : R) (ht : t ≠ 0) : IsOpenMap <| homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]
end Field
end AffineMap