import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
suppress_compilation
open CategoryTheory
universe v u
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace QuadraticModuleCat
open QuadraticForm
instance : BraidedCategory (QuadraticModuleCat.{u} R) :=
  braidedCategoryOfFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))
    (fun X Y => ofIso <| tensorComm X.form Y.form)
    (by aesop_cat)
instance : (forget₂ (QuadraticModuleCat R) (ModuleCat R)).Braided where
instance instSymmetricCategory : SymmetricCategory (QuadraticModuleCat.{u} R) :=
  symmetricCategoryOfFaithful (forget₂ (QuadraticModuleCat R) (ModuleCat R))
end QuadraticModuleCat