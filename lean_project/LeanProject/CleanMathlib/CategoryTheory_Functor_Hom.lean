import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types
universe v u
open Opposite
open CategoryTheory
namespace CategoryTheory.Functor
variable (C : Type u) [Category.{v} C]
@[simps]
def hom : Cᵒᵖ × C ⥤ Type v where
  obj p := unop p.1 ⟶ p.2
  map f h := f.1.unop ≫ h ≫ f.2
end CategoryTheory.Functor