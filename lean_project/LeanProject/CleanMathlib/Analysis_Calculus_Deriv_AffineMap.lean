import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : 𝕜 →ᵃ[𝕜] E) {a b : E} {L : Filter 𝕜} {s : Set 𝕜} {x : 𝕜}
namespace AffineMap
theorem hasStrictDerivAt : HasStrictDerivAt f (f.linear 1) x := by
  rw [f.decomp]
  exact f.linear.hasStrictDerivAt.add_const (f 0)
theorem hasDerivAtFilter : HasDerivAtFilter f (f.linear 1) x L := by
  rw [f.decomp]
  exact f.linear.hasDerivAtFilter.add_const (f 0)
theorem hasDerivWithinAt : HasDerivWithinAt f (f.linear 1) s x := f.hasDerivAtFilter
theorem hasDerivAt : HasDerivAt f (f.linear 1) x := f.hasDerivAtFilter
protected theorem derivWithin (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = f.linear 1 :=
  f.hasDerivWithinAt.derivWithin hs
@[simp] protected theorem deriv : deriv f x = f.linear 1 := f.hasDerivAt.deriv
protected theorem differentiableAt : DifferentiableAt 𝕜 f x := f.hasDerivAt.differentiableAt
protected theorem differentiable : Differentiable 𝕜 f := fun _ ↦ f.differentiableAt
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt
protected theorem differentiableOn : DifferentiableOn 𝕜 f s := fun _ _ ↦ f.differentiableWithinAt
theorem hasStrictDerivAt_lineMap : HasStrictDerivAt (lineMap a b) (b - a) x := by
  simpa using (lineMap a b : 𝕜 →ᵃ[𝕜] E).hasStrictDerivAt
theorem hasDerivAt_lineMap :  HasDerivAt (lineMap a b) (b - a) x :=
  hasStrictDerivAt_lineMap.hasDerivAt
theorem hasDerivWithinAt_lineMap : HasDerivWithinAt (lineMap a b) (b - a) s x :=
  hasDerivAt_lineMap.hasDerivWithinAt
end AffineMap