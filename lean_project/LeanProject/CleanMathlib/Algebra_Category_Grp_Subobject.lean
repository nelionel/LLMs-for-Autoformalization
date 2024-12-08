import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Subobject
open CategoryTheory
universe u
namespace AddCommGrp
instance wellPowered_addCommGrp : WellPowered AddCommGrp.{u} :=
  wellPowered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).asEquivalence
end AddCommGrp