import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
universe u v w
open Topology Filter
open Filter Asymptotics Set
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter 𝕜}
section ContinuousLinearMap
variable (e : 𝕜 →L[𝕜] F)
protected theorem ContinuousLinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.hasFDerivAtFilter.hasDerivAtFilter
protected theorem ContinuousLinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasStrictFDerivAt.hasStrictDerivAt
protected theorem ContinuousLinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
protected theorem ContinuousLinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter
@[simp]
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
protected theorem ContinuousLinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs
end ContinuousLinearMap
section LinearMap
variable (e : 𝕜 →ₗ[𝕜] F)
protected theorem LinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.toContinuousLinearMap₁.hasDerivAtFilter
protected theorem LinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.toContinuousLinearMap₁.hasStrictDerivAt
protected theorem LinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
protected theorem LinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter
@[simp]
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
protected theorem LinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs
end LinearMap