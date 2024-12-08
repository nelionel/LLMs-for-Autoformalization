import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.EssentiallySmall
universe w₁ w₂ v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory
namespace CategoryTheory.Limits
variable (J : Type u₂) [Category.{v₂} J] (C : Type u₁) [Category.{v₁} C]
theorem hasLimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasLimitsOfSize.{w₁, w₁} C] : HasLimitsOfShape J C :=
  hasLimitsOfShape_of_equivalence <| Equivalence.symm <| equivSmallModel.{w₁} J
theorem hasColimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasColimitsOfSize.{w₁, w₁} C] : HasColimitsOfShape J C :=
  hasColimitsOfShape_of_equivalence <| Equivalence.symm <| equivSmallModel.{w₁} J
theorem hasProductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁} C] :
    HasProductsOfShape β C :=
  hasLimitsOfShape_of_equivalence <| Discrete.equivalence <| Equiv.symm <| equivShrink β
theorem hasCoproductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasCoproducts.{w₁} C] :
    HasCoproductsOfShape β C :=
  hasColimitsOfShape_of_equivalence <| Discrete.equivalence <| Equiv.symm <| equivShrink β
end CategoryTheory.Limits