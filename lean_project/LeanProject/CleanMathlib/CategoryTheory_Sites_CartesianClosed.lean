import Mathlib.CategoryTheory.Closed.Ideal
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.ChosenFiniteProducts
noncomputable section
open CategoryTheory Limits
variable {C : Type*} [Category C] (J : GrothendieckTopology C) (A : Type*) [Category A]
instance [HasSheafify J A] [ChosenFiniteProducts A] [CartesianClosed (Cᵒᵖ ⥤ A)] :
    CartesianClosed (Sheaf J A) :=
  cartesianClosedOfReflective (sheafToPresheaf _ _)