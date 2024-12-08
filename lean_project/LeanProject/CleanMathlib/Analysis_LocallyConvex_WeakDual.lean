import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.WeakBilin
variable {𝕜 E F : Type*}
open Topology
section BilinForm
namespace LinearMap
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
def toSeminorm (f : E →ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f
theorem coe_toSeminorm {f : E →ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl
@[simp]
theorem toSeminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl
theorem toSeminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]
theorem toSeminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]
def toSeminormFamily (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm
@[simp]
theorem toSeminormFamily_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl
end LinearMap
end BilinForm
section Topology
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
theorem LinearMap.weakBilin_withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 (WeakBilin B)) :=
  let e : F ≃ (Σ _ : F, Fin 1) := .symm <| .sigmaUnique _ _
  have : Nonempty (Σ _ : F, Fin 1) := e.symm.nonempty
  withSeminorms_induced (withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜 𝕜))
    (LinearMap.ltoFun 𝕜 F 𝕜 ∘ₗ B : (WeakBilin B) →ₗ[𝕜] (F → 𝕜)) |>.congr_equiv e
theorem LinearMap.hasBasis_weakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis B.toSeminormFamily.basisSets _root_.id :=
  LinearMap.weakBilin_withSeminorms B |>.hasBasis
end Topology
section LocallyConvex
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
instance WeakBilin.locallyConvexSpace {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} :
    LocallyConvexSpace ℝ (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace
end LocallyConvex