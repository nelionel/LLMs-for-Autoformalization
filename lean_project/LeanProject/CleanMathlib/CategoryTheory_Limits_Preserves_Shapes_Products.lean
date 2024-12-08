import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Basic
noncomputable section
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
namespace CategoryTheory.Limits
variable {J : Type w} (f : J → C)
def isLimitMapConeFanMkEquiv {P : C} (g : ∀ j, P ⟶ f j) :
    IsLimit (Functor.mapCone G (Fan.mk P g)) ≃
      IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j)) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cones.ext (Iso.refl _) fun j =>
      by dsimp; cases j; simp
def isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ g)) :
    IsLimit (Fan.mk (G.obj P) fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  isLimitMapConeFanMkEquiv _ _ _ (isLimitOfPreserves G t)
def isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j))) :
    IsLimit (Fan.mk P g) :=
  isLimitOfReflects G ((isLimitMapConeFanMkEquiv _ _ _).symm t)
section
variable [HasProduct f]
def isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G] :
    IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j)) :=
  isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)
variable [HasProduct fun j : J => G.obj (f j)]
lemma PreservesProduct.of_iso_comparison [i : IsIso (piComparison G f)] :
    PreservesLimit (Discrete.functor f) G := by
  apply preservesLimit_of_preserves_limit_cone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) i
variable [PreservesLimit (Discrete.functor f) G]
def PreservesProduct.iso : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)
@[simp]
theorem PreservesProduct.iso_hom : (PreservesProduct.iso G f).hom = piComparison G f :=
  rfl
instance : IsIso (piComparison G f) := by
  rw [← PreservesProduct.iso_hom]
  infer_instance
end
def isColimitMapCoconeCofanMkEquiv {P : C} (g : ∀ j, f j ⟶ P) :
    IsColimit (Functor.mapCocone G (Cofan.mk P g)) ≃
      IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j)) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cocones.ext (Iso.refl _) fun j => by dsimp; cases j; simp
def isColimitCofanMkObjOfIsColimit [PreservesColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P) (t : IsColimit (Cofan.mk _ g)) :
    IsColimit (Cofan.mk (G.obj P) fun j => G.map (g j) : Cofan fun j => G.obj (f j)) :=
  isColimitMapCoconeCofanMkEquiv _ _ _ (isColimitOfPreserves G t)
def isColimitOfIsColimitCofanMkObj [ReflectsColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P)
    (t : IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j))) :
    IsColimit (Cofan.mk P g) :=
  isColimitOfReflects G ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)
section
variable [HasCoproduct f]
def isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.functor f) G] :
    IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j => G.obj (f j)) :=
  isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)
variable [HasCoproduct fun j : J => G.obj (f j)]
lemma PreservesCoproduct.of_iso_comparison [i : IsIso (sigmaComparison G f)] :
    PreservesColimit (Discrete.functor f) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _
    (colimit.isColimit (Discrete.functor fun j : J => G.obj (f j))) i
variable [PreservesColimit (Discrete.functor f) G]
def PreservesCoproduct.iso : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)
@[simp]
theorem PreservesCoproduct.inv_hom : (PreservesCoproduct.iso G f).inv = sigmaComparison G f := rfl
instance : IsIso (sigmaComparison G f) := by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance
end
lemma preservesLimitsOfShape_of_discrete (F : C ⥤ D)
    [∀ (f : J → C), PreservesLimit (Discrete.functor f) F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit := preservesLimit_of_iso_diagram F (Discrete.natIsoFunctor).symm
lemma preservesColimitsOfShape_of_discrete (F : C ⥤ D)
    [∀ (f : J → C), PreservesColimit (Discrete.functor f) F] :
    PreservesColimitsOfShape (Discrete J) F where
  preservesColimit := preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor).symm
end CategoryTheory.Limits