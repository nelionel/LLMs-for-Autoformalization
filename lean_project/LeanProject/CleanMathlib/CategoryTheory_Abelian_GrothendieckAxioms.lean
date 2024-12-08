import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
namespace CategoryTheory
open Limits
universe v v' u u' w
variable (C : Type u) [Category.{v} C]
attribute [local instance] hasCoproducts_of_finite_and_filtered
class AB4 [HasCoproducts C] where
  preservesFiniteLimits (α : Type v) :
    PreservesFiniteLimits (colim (J := Discrete α) (C := C))
attribute [instance] AB4.preservesFiniteLimits
class AB4Star [HasProducts C] where
  preservesFiniteColimits (α : Type v) :
    PreservesFiniteColimits (lim (J := Discrete α) (C := C))
attribute [instance] AB4Star.preservesFiniteColimits
class AB5 [HasFilteredColimits C] where
  preservesFiniteLimits (J : Type v) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim (J := J) (C := C))
attribute [instance] AB5.preservesFiniteLimits
class AB5Star [HasCofilteredLimits C] where
  preservesFiniteColimits (J : Type v) [SmallCategory J] [IsCofiltered J] :
    PreservesFiniteColimits (lim (J := J) (C := C))
attribute [instance] AB5Star.preservesFiniteColimits
noncomputable section
open CoproductsFromFiniteFiltered
variable {α : Type w}
variable [HasZeroMorphisms C] [HasFiniteBiproducts C] [HasFiniteLimits C]
instance preservesFiniteLimits_liftToFinset : PreservesFiniteLimits (liftToFinset C α) :=
  preservesFiniteLimits_of_evaluation _ fun I =>
    letI : PreservesFiniteLimits (colim (J := Discrete I) (C := C)) :=
      preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor fun x ↦ ↑x)) :=
      ⟨fun J _ _ => whiskeringLeft_preservesLimitsOfShape J _⟩
    letI : PreservesFiniteLimits ((whiskeringLeft (Discrete I) (Discrete α) C).obj
        (Discrete.functor (·.val)) ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetEvaluationIso  I).symm
lemma AB4.of_AB5 [HasFilteredColimits C] [AB5 C] : AB4 C where
  preservesFiniteLimits J :=
    letI : PreservesFiniteLimits (liftToFinset C J ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    preservesFiniteLimits_of_natIso (liftToFinsetColimIso)
end
end CategoryTheory