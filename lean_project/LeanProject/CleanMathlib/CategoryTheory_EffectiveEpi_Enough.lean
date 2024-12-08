import Mathlib.CategoryTheory.EffectiveEpi.Basic
namespace CategoryTheory
open Limits
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
namespace Functor
structure EffectivePresentation (X : D) where
  p : C
  f : F.obj p ⟶ X
  effectiveEpi : EffectiveEpi f
class EffectivelyEnough : Prop where
  presentation : ∀ (X : D), Nonempty (F.EffectivePresentation X)
variable [F.EffectivelyEnough]
noncomputable def effectiveEpiOverObj (X : D) : D :=
  F.obj (EffectivelyEnough.presentation (F := F) X).some.p
noncomputable def effectiveEpiOver (X : D) : F.effectiveEpiOverObj X ⟶ X :=
  (EffectivelyEnough.presentation X).some.f
instance (X : D) : EffectiveEpi (F.effectiveEpiOver X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi
def equivalenceEffectivePresentation (e : C ≌ D) (X : D) :
    EffectivePresentation e.functor X where
  p := e.inverse.obj X
  f := e.counit.app _
  effectiveEpi := inferInstance
instance [IsEquivalence F] : EffectivelyEnough F where
  presentation X := ⟨equivalenceEffectivePresentation F.asEquivalence X⟩
end Functor
end CategoryTheory