import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
namespace CategoryTheory
noncomputable section
open Category Limits MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type v₂} [Category.{v₁} C]
section CartesianClosed
def Types.tensorProductAdjunction (X : Type v₁) :
    tensorLeft X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
  counit := { app := fun _ xf => xf.2 xf.1 }
instance (X : Type v₁) : (tensorLeft X).IsLeftAdjoint :=
  ⟨_, ⟨Types.tensorProductAdjunction X⟩⟩
instance : CartesianClosed (Type v₁) := CartesianClosed.mk _
  (fun X => Exponentiable.mk _ _ (Types.tensorProductAdjunction X))
instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁) :=
  CartesianClosed.mk _
    (fun F => by
      haveI : ∀ X : Type v₁, PreservesColimits (tensorLeft X) := by infer_instance
      letI : PreservesColimits (tensorLeft F) := ⟨by infer_instance⟩
      have := Presheaf.isLeftAdjoint_of_preservesColimits (tensorLeft F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (tensorLeft F)))
def cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] :
    CartesianClosed (C ⥤ Type (max u₁ v₁ u₂)) :=
  let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((whiskeringLeft _ _ _).obj
        (ULift.equivalence.trans ULiftHom.equiv).functor)
  cartesianClosedOfEquiv e
instance {C : Type u₁} [Category.{v₁} C] : CartesianClosed (C ⥤ Type (max u₁ v₁)) :=
  cartesianClosedFunctorToTypes
instance {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v₁} C] :
    CartesianClosed (C ⥤ Type v₁) :=
  let e : (SmallModel C) ⥤ Type v₁ ≌ C ⥤ Type v₁ :=
    Functor.asEquivalence ((whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e
end CartesianClosed
end
end CategoryTheory