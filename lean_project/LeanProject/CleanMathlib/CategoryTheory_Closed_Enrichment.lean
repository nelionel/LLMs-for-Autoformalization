import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
universe u v
namespace CategoryTheory
namespace MonoidalClosed
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
scoped instance : EnrichedCategory C C where
  Hom x := (ihom x).obj
  id _ := id _
  comp _ _ _ := comp _ _ _
  assoc _ _ _ _ := assoc _ _ _ _
end MonoidalClosed
end CategoryTheory