import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
universe v u w
open CategoryTheory
namespace ModuleCat
variable {k : Type u} [Field k]
variable {A : Type w} [Ring A] [Algebra k A]
def moduleOfAlgebraModule (M : ModuleCat.{v} A) : Module k M :=
  RestrictScalars.module k A M
attribute [scoped instance] ModuleCat.moduleOfAlgebraModule
theorem isScalarTower_of_algebra_moduleCat (M : ModuleCat.{v} A) : IsScalarTower k A M :=
  RestrictScalars.isScalarTower k A M
attribute [scoped instance] ModuleCat.isScalarTower_of_algebra_moduleCat
example (M N : ModuleCat.{v} A) : Module k (M ⟶ N) := LinearMap.module
instance linearOverField : Linear k (ModuleCat.{v} A) where
  homModule _ _ := LinearMap.module
  smul_comp := by
    intros
    ext
    dsimp only [coe_comp, Function.comp_apply]
    rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower]
    rfl
end ModuleCat