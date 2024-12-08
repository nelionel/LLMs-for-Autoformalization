import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
open Asymptotics
section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s : Set E}
variable {L : Filter E}
section ContinuousLinearMap
@[fun_prop]
protected theorem ContinuousLinearMap.hasStrictFDerivAt {x : E} : HasStrictFDerivAt e e x :=
  .of_isLittleO <| (isLittleO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]
protected theorem ContinuousLinearMap.hasFDerivAtFilter : HasFDerivAtFilter e e x L :=
  .of_isLittleO <| (isLittleO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]
@[fun_prop]
protected theorem ContinuousLinearMap.hasFDerivWithinAt : HasFDerivWithinAt e e s x :=
  e.hasFDerivAtFilter
@[fun_prop]
protected theorem ContinuousLinearMap.hasFDerivAt : HasFDerivAt e e x :=
  e.hasFDerivAtFilter
@[simp, fun_prop]
protected theorem ContinuousLinearMap.differentiableAt : DifferentiableAt 𝕜 e x :=
  e.hasFDerivAt.differentiableAt
@[fun_prop]
protected theorem ContinuousLinearMap.differentiableWithinAt : DifferentiableWithinAt 𝕜 e s x :=
  e.differentiableAt.differentiableWithinAt
@[simp]
protected theorem ContinuousLinearMap.fderiv : fderiv 𝕜 e x = e :=
  e.hasFDerivAt.fderiv
protected theorem ContinuousLinearMap.fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 e s x = e := by
  rw [DifferentiableAt.fderivWithin e.differentiableAt hxs]
  exact e.fderiv
@[simp, fun_prop]
protected theorem ContinuousLinearMap.differentiable : Differentiable 𝕜 e := fun _ =>
  e.differentiableAt
@[fun_prop]
protected theorem ContinuousLinearMap.differentiableOn : DifferentiableOn 𝕜 e s :=
  e.differentiable.differentiableOn
theorem IsBoundedLinearMap.hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAtFilter f h.toContinuousLinearMap x L :=
  h.toContinuousLinearMap.hasFDerivAtFilter
@[fun_prop]
theorem IsBoundedLinearMap.hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivWithinAt f h.toContinuousLinearMap s x :=
  h.hasFDerivAtFilter
@[fun_prop]
theorem IsBoundedLinearMap.hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAt f h.toContinuousLinearMap x :=
  h.hasFDerivAtFilter
@[fun_prop]
theorem IsBoundedLinearMap.differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt
@[fun_prop]
theorem IsBoundedLinearMap.differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt
theorem IsBoundedLinearMap.fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFDerivAt.fderiv h.hasFDerivAt
theorem IsBoundedLinearMap.fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap := by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv
@[fun_prop]
theorem IsBoundedLinearMap.differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun _ => h.differentiableAt
@[fun_prop]
theorem IsBoundedLinearMap.differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiableOn
end ContinuousLinearMap
end