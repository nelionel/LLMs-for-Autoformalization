import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
open CategoryTheory Limits Monoidal MonoidalCategory
universe v u w
noncomputable section
namespace Mon_
variable {J : Type w} [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasLimitsOfShape J C] [MonoidalCategory.{v} C]
@[simps!]
def limit (F : J ⥤ Mon_ C) : Mon_ C :=
  lim.mapMon.obj ((monFunctorCategoryEquivalence J C).inverse.obj F)
@[simps]
def limitCone (F : J ⥤ Mon_ C) : Cone F where
  pt := limit F
  π :=
    { app := fun j => { hom := limit.π (F ⋙ Mon_.forget C) j }
      naturality := fun j j' f => by ext; exact (limit.cone (F ⋙ Mon_.forget C)).π.naturality f }
def forgetMapConeLimitConeIso (F : J ⥤ Mon_ C) :
    (forget C).mapCone (limitCone F) ≅ limit.cone (F ⋙ forget C) :=
  Cones.ext (Iso.refl _) (by aesop_cat)
@[simps]
def limitConeIsLimit (F : J ⥤ Mon_ C) : IsLimit (limitCone F) where
  lift s :=
    { hom := limit.lift (F ⋙ Mon_.forget C) ((Mon_.forget C).mapCone s)
      mul_hom := limit.hom_ext (fun j ↦ by
        dsimp
        simp only [Category.assoc, limit.lift_π, Functor.mapCone_pt, forget_obj,
          Functor.mapCone_π_app, forget_map, Hom.mul_hom, limMap_π, tensorObj_obj, Functor.comp_obj,
          MonFunctorCategoryEquivalence.inverseObj_mul_app, lim_μ_π_assoc, lim_obj,
          ← MonoidalCategory.tensor_comp_assoc]) }
  fac s h := by ext; simp
  uniq s m w := by
    ext1
    refine limit.hom_ext (fun j => ?_)
    dsimp; simp only [Mon_.forget_map, limit.lift_π, Functor.mapCone_π_app]
    exact congr_arg Mon_.Hom.hom (w j)
instance hasLimitsOfShape [HasLimitsOfShape J C] : HasLimitsOfShape J (Mon_ C) where
  has_limit := fun F => HasLimit.mk
    { cone := limitCone F
      isLimit := limitConeIsLimit F }
instance forget_freservesLimitsOfShape : PreservesLimitsOfShape J (Mon_.forget C) where
  preservesLimit := fun {F} =>
    preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
      (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ Mon_.forget C)) (forgetMapConeLimitConeIso F).symm)
end Mon_