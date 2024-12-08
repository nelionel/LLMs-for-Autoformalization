import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.Sites.LeftExact
universe u
noncomputable section
open CategoryTheory
instance : ChosenFiniteProducts (CondensedSet.{u}) :=
  inferInstanceAs (ChosenFiniteProducts (Sheaf _ _))
instance : CartesianClosed (CondensedSet.{u}) := inferInstanceAs (CartesianClosed (Sheaf _ _))