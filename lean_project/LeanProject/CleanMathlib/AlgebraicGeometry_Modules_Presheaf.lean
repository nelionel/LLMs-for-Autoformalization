import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Whiskering
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u})
abbrev ringCatSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf
nonrec abbrev PresheafOfModules := PresheafOfModules.{u} X.ringCatSheaf.val
end AlgebraicGeometry.Scheme