import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
universe w' w v v' u' u
namespace SheafOfModules
open CategoryTheory Limits
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrp.{v}]
  [J.WEqualsLocallyBijective AddCommGrp.{v}] (K : Type w) [Category.{w'} K]
instance [HasColimitsOfShape K (PresheafOfModules.{v} R.val)] :
    HasColimitsOfShape K (SheafOfModules.{v} R) where
  has_colimit F := by
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.val) :=
      isoWhiskerLeft F (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).counit).symm
    exact hasColimitOfIso e
end SheafOfModules