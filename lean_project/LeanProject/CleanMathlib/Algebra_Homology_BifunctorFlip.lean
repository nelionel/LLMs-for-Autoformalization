import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.TotalComplexSymmetry
open CategoryTheory Limits
variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
namespace HomologicalComplex
variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]
lemma hasMapBifunctor_flip_iff :
    HasMapBifunctor K₂ K₁ F.flip c ↔ HasMapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_hasTotal_iff c
variable [DecidableEq J] [HasMapBifunctor K₁ K₂ F c]
instance : HasMapBifunctor K₂ K₁ F.flip c := by
  rw [hasMapBifunctor_flip_iff]
  infer_instance
noncomputable def mapBifunctorFlipIso :
    mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).totalFlipIso c
lemma mapBifunctorFlipIso_flip
    [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c] :
    mapBifunctorFlipIso K₂ K₁ F.flip c = (mapBifunctorFlipIso K₁ K₂ F c).symm :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_totalFlipIso c
end HomologicalComplex