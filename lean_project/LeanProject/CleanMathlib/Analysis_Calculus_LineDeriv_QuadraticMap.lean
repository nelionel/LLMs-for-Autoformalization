import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.QuadraticForm.Basic
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
namespace QuadraticMap
theorem hasLineDerivAt (f : QuadraticMap 𝕜 E F) (a b : E) :
    HasLineDerivAt 𝕜 f (polar f a b) a b := by
  simpa [HasLineDerivAt, QuadraticMap.map_add, f.map_smul] using
    ((hasDerivAt_const (0 : 𝕜) (f a)).add <|
      ((hasDerivAt_id 0).mul (hasDerivAt_id 0)).smul (hasDerivAt_const 0 (f b))).add
      ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (polar f a b)))
theorem lineDifferentiableAt (f : QuadraticMap 𝕜 E F) (a b : E) : LineDifferentiableAt 𝕜 f a b :=
  (f.hasLineDerivAt a b).lineDifferentiableAt
@[simp]
protected theorem lineDeriv (f : QuadraticMap 𝕜 E F) : lineDeriv 𝕜 f = polar f := by
  ext a b
  exact (f.hasLineDerivAt a b).lineDeriv
end QuadraticMap