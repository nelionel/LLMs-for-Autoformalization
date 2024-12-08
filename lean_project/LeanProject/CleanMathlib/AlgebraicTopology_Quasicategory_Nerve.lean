import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
universe v u
open SSet
namespace CategoryTheory.Nerve
instance quasicategory {C : Type u} [Category.{v} C] :
  Quasicategory (nerve C) := inferInstance
end CategoryTheory.Nerve