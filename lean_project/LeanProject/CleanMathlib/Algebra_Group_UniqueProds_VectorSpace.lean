import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
variable {G : Type*}
instance [AddCommGroup G] [Module ℚ G] : TwoUniqueSums G :=
  TwoUniqueSums.of_injective_addHom _ (Basis.ofVectorSpace ℚ G).repr.injective inferInstance