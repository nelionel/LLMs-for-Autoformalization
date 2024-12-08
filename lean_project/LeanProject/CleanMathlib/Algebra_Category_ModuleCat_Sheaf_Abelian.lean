import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.Transfer
universe v v' u u'
open CategoryTheory Limits
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
namespace SheafOfModules
variable (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrp.{v}]
  [J.WEqualsLocallyBijective AddCommGrp.{v}]
noncomputable instance : Abelian (SheafOfModules.{v} R) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.val)
  exact abelianOfAdjunction _ _ (asIso (adj.counit)) adj
end SheafOfModules