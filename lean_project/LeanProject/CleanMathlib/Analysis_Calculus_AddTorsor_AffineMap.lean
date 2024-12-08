import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
namespace ContinuousAffineMap
variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
theorem contDiff {n : WithTop ℕ∞} (f : V →ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const
end ContinuousAffineMap