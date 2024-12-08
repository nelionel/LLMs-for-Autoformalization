import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Preserves.Limits
universe w v₁ v u₁ u
namespace CategoryTheory
open Limits Opposite
variable {C : Type u} [Category.{v} C]
namespace CategoryOfElements
variable {A : C ⥤ Type w} {I : Type u₁} [Category.{v₁} I] [Small.{w} I]
namespace CreatesLimitsAux
variable (F : I ⥤ A.Elements)
noncomputable def liftedConeElement' : limit ((F ⋙ π A) ⋙ A) :=
  Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)
@[simp]
lemma π_liftedConeElement' (i : I) :
    limit.π ((F ⋙ π A) ⋙ A) i (liftedConeElement' F) = (F.obj i).2 :=
  Types.Limit.π_mk _ _ _ _
variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]
noncomputable def liftedConeElement : A.obj (limit (F ⋙ π A)) :=
  (preservesLimitIso A (F ⋙ π A)).inv (liftedConeElement' F)
@[simp]
lemma map_lift_mapCone (c : Cone F) :
    A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd = liftedConeElement F := by
  apply (preservesLimitIso A (F ⋙ π A)).toEquiv.injective
  ext i
  have h₁ := congrFun (preservesLimitIso_hom_π A (F ⋙ π A) i)
    (A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd)
  have h₂ := (c.π.app i).property
  simp_all [← FunctorToTypes.map_comp_apply, liftedConeElement]
@[simp]
lemma map_π_liftedConeElement (i : I) :
    A.map (limit.π (F ⋙ π A) i) (liftedConeElement F) = (F.obj i).snd := by
  have := congrFun
    (preservesLimitIso_inv_π A (F ⋙ π A) i) (liftedConeElement' F)
  simp_all [liftedConeElement]
@[simps]
noncomputable def liftedCone : Cone F where
  pt := ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simp⟩
      naturality := fun i i' f => by ext; simpa using (limit.w _ _).symm }
noncomputable def isValidLift : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A) :=
  Iso.refl _
noncomputable def isLimit : IsLimit (liftedCone F) where
  lift s := ⟨limit.lift (F ⋙ π A) ((π A).mapCone s), by simp⟩
  uniq s m h := ext _ _ _ <| limit.hom_ext
    fun i => by simpa using congrArg Subtype.val (h i)
end CreatesLimitsAux
variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]
section
open CreatesLimitsAux
noncomputable instance (F : I ⥤ A.Elements) : CreatesLimit F (π A) :=
  createsLimitOfReflectsIso' (limit.isLimit _) ⟨⟨liftedCone F, isValidLift F⟩, isLimit F⟩
end
noncomputable instance : CreatesLimitsOfShape I (π A) where
instance : HasLimitsOfShape I A.Elements :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (π A)
end CategoryOfElements
end CategoryTheory