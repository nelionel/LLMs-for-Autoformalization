import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Light.Basic
universe u
noncomputable section
open CategoryTheory
variable {C : Type u} [SmallCategory C]
instance : ChosenFiniteProducts (LightCondSet.{u}) :=
  inferInstanceAs (ChosenFiniteProducts (Sheaf _ _))
instance : CartesianClosed (LightCondSet.{u}) := inferInstanceAs (CartesianClosed (Sheaf _ _))