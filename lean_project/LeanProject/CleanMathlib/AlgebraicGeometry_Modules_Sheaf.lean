import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Modules.Presheaf
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u})
abbrev Modules := SheafOfModules.{u} X.ringCatSheaf
noncomputable instance : Abelian X.Modules := inferInstance
end AlgebraicGeometry.Scheme