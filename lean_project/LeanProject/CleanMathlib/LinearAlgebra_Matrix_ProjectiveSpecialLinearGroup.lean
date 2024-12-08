import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
namespace Matrix
universe u v
open Matrix LinearMap
open scoped MatrixGroups
variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ Subgroup.center (SpecialLinearGroup n R)
scoped[MatrixGroups] notation "PSL(" n ", " R ")" => Matrix.ProjectiveSpecialLinearGroup (Fin n) R
end Matrix