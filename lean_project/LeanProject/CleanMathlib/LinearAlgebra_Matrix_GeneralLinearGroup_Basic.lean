import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
namespace Matrix
section Examples
@[simps! (config := .asFn) val]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)
end Examples
end Matrix