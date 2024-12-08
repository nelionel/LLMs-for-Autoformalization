import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Symmetric
import Mathlib.CategoryTheory.Monoidal.Types.Basic
open CategoryTheory Limits
universe v u
namespace CategoryTheory
open MonoidalCategory
instance typesSymmetric : SymmetricCategory.{u} (Type u) :=
  symmetricOfChosenFiniteProducts Types.terminalLimitCone Types.binaryProductLimitCone
@[simp]
theorem braiding_hom_apply {X Y : Type u} {x : X} {y : Y} :
    ((β_ X Y).hom : X ⊗ Y → Y ⊗ X) (x, y) = (y, x) :=
  rfl
@[simp]
theorem braiding_inv_apply {X Y : Type u} {x : X} {y : Y} :
    ((β_ X Y).inv : Y ⊗ X → X ⊗ Y) (y, x) = (x, y) :=
  rfl
end CategoryTheory