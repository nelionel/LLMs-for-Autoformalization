import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Functor
namespace CategoryTheory
variable (C : Type*) [Category C] [MonoidalCategory C]
@[nolint unusedArguments]
def MonoidalSingleObj (C : Type*) [Category C] [MonoidalCategory C] :=
  PUnit 
instance : Inhabited (MonoidalSingleObj C) := by
  unfold MonoidalSingleObj
  infer_instance
open MonoidalCategory
instance : Bicategory (MonoidalSingleObj C) where
  Hom _ _ := C
  id _ := 𝟙_ C
  comp X Y := tensorObj X Y
  whiskerLeft X _ _ f := X ◁ f
  whiskerRight f Z := f ▷ Z
  associator X Y Z := α_ X Y Z
  leftUnitor X := λ_ X
  rightUnitor X := ρ_ X
  whisker_exchange := whisker_exchange
namespace MonoidalSingleObj
@[nolint unusedArguments]
protected def star : MonoidalSingleObj C :=
  PUnit.unit
@[simps]
def endMonoidalStarFunctor : (EndMonoidal (MonoidalSingleObj.star C)) ⥤ C where
  obj X := X
  map f := f
instance : (endMonoidalStarFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }
@[simps]
noncomputable def endMonoidalStarFunctorEquivalence :
    EndMonoidal (MonoidalSingleObj.star C) ≌ C where
  functor := endMonoidalStarFunctor C
  inverse :=
    { obj := fun X => X
      map := fun f => f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
instance endMonoidalStarFunctor_isEquivalence : (endMonoidalStarFunctor C).IsEquivalence :=
  (endMonoidalStarFunctorEquivalence C).isEquivalence_functor
end MonoidalSingleObj
end CategoryTheory