import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Generator
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Subobject.Comma
universe v u u'
namespace CategoryTheory
open Limits
variable {J : Type v}
variable {C : Type u} [Category.{v} C]
def SolutionSetCondition {D : Type u} [Category.{v} D] (G : D ⥤ C) : Prop :=
  ∀ A : C,
    ∃ (ι : Type v) (B : ι → D) (f : ∀ i : ι, A ⟶ G.obj (B i)),
      ∀ (X) (h : A ⟶ G.obj X), ∃ (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h
section GeneralAdjointFunctorTheorem
variable {D : Type u} [Category.{v} D]
variable (G : D ⥤ C)
theorem solutionSetCondition_of_isRightAdjoint [G.IsRightAdjoint] : SolutionSetCondition G := by
  intro A
  refine
    ⟨PUnit, fun _ => G.leftAdjoint.obj A, fun _ => (Adjunction.ofIsRightAdjoint G).unit.app A, ?_⟩
  intro B h
  refine ⟨PUnit.unit, ((Adjunction.ofIsRightAdjoint G).homEquiv _ _).symm h, ?_⟩
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
lemma isRightAdjoint_of_preservesLimits_of_solutionSetCondition [HasLimits D]
    [PreservesLimits G] (hG : SolutionSetCondition G) : G.IsRightAdjoint := by
  refine @isRightAdjointOfStructuredArrowInitials _ _ _ _ G ?_
  intro A
  specialize hG A
  choose ι B f g using hG
  let B' : ι → StructuredArrow A G := fun i => StructuredArrow.mk (f i)
  have hB' : ∀ A' : StructuredArrow A G, ∃ i, Nonempty (B' i ⟶ A') := by
    intro A'
    obtain ⟨i, _, t⟩ := g _ A'.hom
    exact ⟨i, ⟨StructuredArrow.homMk _ t⟩⟩
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts hB'
  apply hasInitial_of_weakly_initial_and_hasWideEqualizers hT
end GeneralAdjointFunctorTheorem
section SpecialAdjointFunctorTheorem
variable {D : Type u'} [Category.{v} D]
lemma isRightAdjoint_of_preservesLimits_of_isCoseparating [HasLimits D] [WellPowered D]
    {𝒢 : Set D} [Small.{v} 𝒢] (h𝒢 : IsCoseparating 𝒢) (G : D ⥤ C) [PreservesLimits G] :
    G.IsRightAdjoint :=
  have : ∀ A, HasInitial (StructuredArrow A G) := fun A =>
    hasInitial_of_isCoseparating (StructuredArrow.isCoseparating_proj_preimage A G h𝒢)
  isRightAdjointOfStructuredArrowInitials _
lemma isLeftAdjoint_of_preservesColimits_of_isSeparating [HasColimits C] [WellPowered Cᵒᵖ]
    {𝒢 : Set C} [Small.{v} 𝒢] (h𝒢 : IsSeparating 𝒢) (F : C ⥤ D) [PreservesColimits F] :
    F.IsLeftAdjoint :=
  have : ∀ A, HasTerminal (CostructuredArrow F A) := fun A =>
    hasTerminal_of_isSeparating (CostructuredArrow.isSeparating_proj_preimage F A h𝒢)
  isLeftAdjoint_of_costructuredArrowTerminals _
end SpecialAdjointFunctorTheorem
namespace Limits
theorem hasColimits_of_hasLimits_of_isCoseparating [HasLimits C] [WellPowered C] {𝒢 : Set C}
    [Small.{v} 𝒢] (h𝒢 : IsCoseparating 𝒢) : HasColimits C :=
  { has_colimits_of_shape := fun _ _ =>
      hasColimitsOfShape_iff_isRightAdjoint_const.2
        (isRightAdjoint_of_preservesLimits_of_isCoseparating h𝒢 _) }
theorem hasLimits_of_hasColimits_of_isSeparating [HasColimits C] [WellPowered Cᵒᵖ] {𝒢 : Set C}
    [Small.{v} 𝒢] (h𝒢 : IsSeparating 𝒢) : HasLimits C :=
  { has_limits_of_shape := fun _ _ =>
      hasLimitsOfShape_iff_isLeftAdjoint_const.2
        (isLeftAdjoint_of_preservesColimits_of_isSeparating h𝒢 _) }
end Limits
end CategoryTheory