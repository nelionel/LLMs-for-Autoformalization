import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
open CategoryTheory Limits
universe u
noncomputable section
namespace AddCommGrp
variable {X Y Z : AddCommGrp.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).inv <|
    ModuleCat.normalMono _ inferInstance
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance
instance : Abelian AddCommGrp.{u} where
  has_finite_products := ⟨HasFiniteProducts.out⟩
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi
end AddCommGrp