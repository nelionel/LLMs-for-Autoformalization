import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Filtered
universe w' w v₁ v₂ u₁ u₂
namespace CategoryTheory.Limits
variable {C : Type u₁} [Category.{v₁} C] {K : Type u₂} [Category.{v₂} K]
instance [HasFilteredColimitsOfSize.{w', w} C] : HasFilteredColimitsOfSize.{w', w} (K ⥤ C) :=
  ⟨fun _ => inferInstance⟩
instance [HasCofilteredLimitsOfSize.{w', w} C] : HasCofilteredLimitsOfSize.{w', w} (K ⥤ C) :=
  ⟨fun _ => inferInstance⟩
end CategoryTheory.Limits