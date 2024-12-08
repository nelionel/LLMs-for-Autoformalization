import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.MorphismProperty.Limits
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open Limits
namespace Localization
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  {W : MorphismProperty C} [L.IsLocalization W]
namespace HasProductsOfShapeAux
variable {J : Type} [HasProductsOfShape J C]
  (hW : W.IsStableUnderProductsOfShape J)
include hW
lemma inverts :
    (W.functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (hW.lim_map f hf)
variable [W.ContainsIdentities] [Finite J]
noncomputable abbrev limitFunctor :
    (Discrete J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts L hW)
    ((whiskeringRight (Discrete J) C D).obj L)
noncomputable def compLimitFunctorIso :
    ((whiskeringRight (Discrete J) C D).obj L) ⋙ limitFunctor L hW ≅
      lim ⋙ L := by
  apply Localization.fac
instance :
    CatCommSq (Functor.const (Discrete J)) L
      ((whiskeringRight (Discrete J) C D).obj L) (Functor.const (Discrete J)) where
  iso' := (Functor.compConstIso _ _).symm
noncomputable instance :
    CatCommSq lim ((whiskeringRight (Discrete J) C D).obj L) L (limitFunctor L hW) where
  iso' := (compLimitFunctorIso L hW).symm
noncomputable def adj :
    Functor.const _ ⊣ limitFunctor L hW :=
  constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L hW)
lemma adj_counit_app (F : Discrete J ⥤ C) :
    (adj L hW).counit.app (F ⋙ L) =
      (Functor.const (Discrete J)).map ((compLimitFunctorIso L hW).hom.app F) ≫
        (Functor.compConstIso (Discrete J) L).hom.app (lim.obj F) ≫
        whiskerRight (constLimAdj.counit.app F) L := by
  apply constLimAdj.localization_counit_app
noncomputable def isLimitMapCone (F : Discrete J ⥤ C) :
    IsLimit (L.mapCone (limit.cone F)) :=
  IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L hW) (F ⋙ L))
    (Cones.ext ((compLimitFunctorIso L hW).app F) (by simp [adj_counit_app, constLimAdj]))
end HasProductsOfShapeAux
variable (W)
variable [W.ContainsIdentities]
include L
lemma hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C]
    (hW : W.IsStableUnderProductsOfShape J) :
    HasProductsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L hW).isLeftAdjoint
lemma preservesProductsOfShape (J : Type) [Finite J]
    [HasProductsOfShape J C] (hW : W.IsStableUnderProductsOfShape J) :
    PreservesLimitsOfShape (Discrete J) L where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L hW F)
variable [HasFiniteProducts C] [W.IsStableUnderFiniteProducts]
include W in
lemma hasFiniteProducts : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _
    (W.isStableUnderProductsOfShape_of_isStableUnderFiniteProducts _)⟩
include W in
lemma preservesFiniteProducts :
    PreservesFiniteProducts L where
  preserves J _ := preservesProductsOfShape L W J
      (W.isStableUnderProductsOfShape_of_isStableUnderFiniteProducts _)
instance : HasFiniteProducts (W.Localization) := hasFiniteProducts W.Q W
noncomputable instance : PreservesFiniteProducts W.Q := preservesFiniteProducts W.Q W
instance [W.HasLocalization] :
    HasFiniteProducts (W.Localization') :=
  hasFiniteProducts W.Q' W
noncomputable instance [W.HasLocalization] :
    PreservesFiniteProducts W.Q' :=
  preservesFiniteProducts W.Q' W
end Localization
end CategoryTheory