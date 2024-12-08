import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
namespace CategoryTheory
variable (R : Type*) [Semiring R]
class Functor.Linear {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [Linear R C] [Linear R D] (F : C ⥤ D) [F.Additive] : Prop where
  map_smul : ∀ {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f := by aesop_cat
section Linear
namespace Functor
section
variable {R}
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] (F : C ⥤ D) [Additive F] [Linear R F]
@[simp]
theorem map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
  Functor.Linear.map_smul _ _
@[simp]
theorem map_units_smul {X Y : C} (r : Rˣ) (f : X ⟶ Y) : F.map (r • f) = r • F.map f := by
  apply map_smul
instance : Linear R (𝟭 C) where
instance {E : Type*} [Category E] [Preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E)
    [Additive G] [Linear R G] : Linear R (F ⋙ G) where
variable (R)
@[simps]
def mapLinearMap {X Y : C} : (X ⟶ Y) →ₗ[R] F.obj X ⟶ F.obj Y :=
  { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }
theorem coe_mapLinearMap {X Y : C} : ⇑(F.mapLinearMap R : (X ⟶ Y) →ₗ[R] _) = F.map := rfl
end
section InducedCategory
variable {C : Type*} {D : Type*} [Category D] [Preadditive D] [CategoryTheory.Linear R D]
  (F : C → D)
instance inducedFunctorLinear : Functor.Linear R (inducedFunctor F) where
end InducedCategory
instance fullSubcategoryInclusionLinear {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear R C] (Z : C → Prop) : (fullSubcategoryInclusion Z).Linear R where
section
variable {R} {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
  [Additive F]
instance natLinear : F.Linear ℕ where
  map_smul := F.mapAddHom.map_nsmul
instance intLinear : F.Linear ℤ where
  map_smul f r := F.mapAddHom.map_zsmul f r
variable [CategoryTheory.Linear ℚ C] [CategoryTheory.Linear ℚ D]
instance ratLinear : F.Linear ℚ where
  map_smul f r := F.mapAddHom.toRatLinearMap.map_smul r f
end
end Functor
namespace Equivalence
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Linear R C] [Preadditive D]
  [Linear R D]
instance inverseLinear (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] :
  e.inverse.Linear R where
    map_smul r f := by
      apply e.functor.map_injective
      simp
end Equivalence
end Linear
end CategoryTheory