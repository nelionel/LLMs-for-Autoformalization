import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Orientation
namespace Complex
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.orientation
end Complex