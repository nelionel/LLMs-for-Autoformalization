import Mathlib.CategoryTheory.Adjunction.Lifting.Right
import Mathlib.CategoryTheory.Closed.FunctorCategory.Groupoid
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monad.Comonadicity
universe v₁ v₂ u₁ u₂
open CategoryTheory MonoidalCategory MonoidalClosed Limits
noncomputable section
namespace CategoryTheory.Functor
section
variable (I : Type u₂) [Category.{v₂} I]
private abbrev incl : Discrete I ⥤ I := Discrete.functor id
variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
variable [∀ (F : Discrete I ⥤ C), (Discrete.functor id).HasRightKanExtension F]
instance : ReflectsIsomorphisms <| (whiskeringLeft _ _ C).obj (incl I) where
  reflects f h := by
    simp only [NatTrans.isIso_iff_isIso_app] at *
    intro X
    exact h ⟨X⟩
variable [HasLimitsOfShape WalkingParallelPair C]
instance : Comonad.PreservesLimitOfIsCoreflexivePair ((whiskeringLeft _ _ C).obj (incl I)) :=
  ⟨inferInstance⟩
instance : ComonadicLeftAdjoint ((whiskeringLeft _ _ C).obj (incl I)) :=
  Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms
    ((incl I).ranAdjunction C)
instance (F : I ⥤ C) : IsLeftAdjoint (tensorLeft (incl I ⋙ F)) :=
  (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint
def functorCategoryClosed (F : I ⥤ C) : Closed F :=
  have := (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint
  have := isLeftAdjoint_square_lift_comonadic (tensorLeft F) ((whiskeringLeft _ _ C).obj (incl I))
    ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  { rightAdj := (tensorLeft F).rightAdjoint
    adj := Adjunction.ofIsLeftAdjoint (tensorLeft F) }
def functorCategoryMonoidalClosed : MonoidalClosed (I ⥤ C) where
  closed F := functorCategoryClosed I C F
end
end CategoryTheory.Functor