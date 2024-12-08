import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
universe w v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
open Category DerivedCategory Pretriangulated
namespace ShortComplex
variable {S : ShortComplex C} (hS : S.ShortExact)
namespace ShortExact
noncomputable def singleδ : (singleFunctor C 0).obj S.X₃ ⟶
    ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (singleFunctorsPostcompQIso C)).inv.app S.X₁)⟦(1 : ℤ)⟧'
@[simps!]
noncomputable def singleTriangle : Triangle (DerivedCategory C) :=
  Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) hS.singleδ
@[simps!]
noncomputable def singleTriangleIso :
    hS.singleTriangle ≅
      triangleOfSES (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
  let e := (SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)
  refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
  · aesop_cat
  · aesop_cat
  · dsimp [singleδ, e]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, SingleFunctors.inv_hom_id_hom_app]
    erw [Functor.map_id, comp_id]
lemma singleTriangle_distinguished :
    hS.singleTriangle ∈ distTriang (DerivedCategory C) :=
  isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0))) _ (singleTriangleIso hS)
end ShortExact
end ShortComplex
end CategoryTheory