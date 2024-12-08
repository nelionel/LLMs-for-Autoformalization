import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Metrizable.Basic
open Set Function Filter CauSeq UniformSpace
theorem Rat.uniformSpace_eq :
    (AbsoluteValue.abs : AbsoluteValue ℚ ℚ).uniformSpace = PseudoMetricSpace.toUniformSpace := by
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity _).mem_iff, Metric.uniformity_basis_dist_rat.mem_iff]
  simp only [Rat.dist_eq, AbsoluteValue.abs_apply, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_lt,
    abs_sub_comm]
def rationalCauSeqPkg : @AbstractCompletion ℚ <| (@AbsoluteValue.abs ℚ _).uniformSpace :=
  @AbstractCompletion.mk
    (space := ℝ)
    (coe := ((↑) : ℚ → ℝ))
    (uniformStruct := by infer_instance)
    (complete := by infer_instance)
    (separation := by infer_instance)
    (isUniformInducing := by
      rw [Rat.uniformSpace_eq]
      exact Rat.isUniformEmbedding_coe_real.isUniformInducing)
    (dense := Rat.isDenseEmbedding_coe_real.dense)
namespace CompareReals
def Q :=
  ℚ deriving CommRing, Inhabited
instance uniformSpace : UniformSpace Q :=
  (@AbsoluteValue.abs ℚ _).uniformSpace
def Bourbakiℝ : Type :=
  Completion Q deriving Inhabited
instance Bourbaki.uniformSpace : UniformSpace Bourbakiℝ :=
  Completion.uniformSpace Q
def bourbakiPkg : AbstractCompletion Q :=
  Completion.cPkg
noncomputable def compareEquiv : Bourbakiℝ ≃ᵤ ℝ :=
  bourbakiPkg.compareEquiv rationalCauSeqPkg
theorem compare_uc : UniformContinuous compareEquiv :=
  bourbakiPkg.uniformContinuous_compareEquiv rationalCauSeqPkg
theorem compare_uc_symm : UniformContinuous compareEquiv.symm :=
  bourbakiPkg.uniformContinuous_compareEquiv_symm rationalCauSeqPkg
end CompareReals