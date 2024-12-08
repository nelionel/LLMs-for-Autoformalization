import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
noncomputable section
open Topology Bornology NNReal uniformity UniformConvergence
open Set Filter Metric Function
universe u v w
variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}
namespace BoundedContinuousFunction
section NormedAddCommGroup
variable {𝕜 : Type*} [NormedField 𝕜] [StarRing 𝕜] [TopologicalSpace α] [SeminormedAddCommGroup β]
  [StarAddMonoid β] [NormedStarGroup β]
variable [NormedSpace 𝕜 β] [StarModule 𝕜 β]
instance instStarAddMonoid : StarAddMonoid (α →ᵇ β) where
  star f := f.comp star starNormedAddGroupHom.lipschitz
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)
@[simp]
theorem coe_star (f : α →ᵇ β) : ⇑(star f) = star (⇑f) := rfl
@[simp]
theorem star_apply (f : α →ᵇ β) (x : α) : star f x = star (f x) := rfl
instance instNormedStarGroup : NormedStarGroup (α →ᵇ β) where
  norm_star f := by simp only [norm_eq, star_apply, norm_star]
instance instStarModule : StarModule 𝕜 (α →ᵇ β) where
  star_smul k f := ext fun x => star_smul k (f x)
end NormedAddCommGroup
section CStarRing
variable [TopologicalSpace α]
variable [NonUnitalNormedRing β] [StarRing β]
instance instStarRing [NormedStarGroup β] : StarRing (α →ᵇ β) where
  __ := instStarAddMonoid
  star_mul f g := ext fun x ↦ star_mul (f x) (g x)
variable [CStarRing β]
instance instCStarRing : CStarRing (α →ᵇ β) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _), norm_le (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact norm_coe_le_norm (star f * f) x
end CStarRing
end BoundedContinuousFunction