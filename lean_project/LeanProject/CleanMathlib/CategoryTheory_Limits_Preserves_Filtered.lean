import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Filtered.Basic
open CategoryTheory
open CategoryTheory.Functor
namespace CategoryTheory.Limits
universe w' w₂' w w₂ v u₁ u₂ u₃
variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {E : Type u₃} [Category.{v} E]
variable {J : Type v} [SmallCategory J] {K : J ⥤ C}
section FilteredColimits
section Preserves
@[nolint checkUnivs, pp_with_univ]
class PreservesFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  preserves_filtered_colimits :
    ∀ (J : Type w) [Category.{w'} J] [IsFiltered J], PreservesColimitsOfShape J F
abbrev PreservesFilteredColimits (F : C ⥤ D) : Prop :=
  PreservesFilteredColimitsOfSize.{v, v} F
attribute [instance 100] PreservesFilteredColimitsOfSize.preserves_filtered_colimits
instance (priority := 100) PreservesColimits.preservesFilteredColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w'} F] : PreservesFilteredColimitsOfSize.{w, w'} F where
  preserves_filtered_colimits _ := inferInstance
instance comp_preservesFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFilteredColimitsOfSize.{w, w'} F] [PreservesFilteredColimitsOfSize.{w, w'} G] :
      PreservesFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_filtered_colimits _ := inferInstance
lemma preservesFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesFilteredColimitsOfSize.{w', w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w₂} F where
  preserves_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm
    haveI := IsFiltered.of_equivalence e.symm
    exact preservesColimitsOfShape_of_equiv e F
lemma preservesFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w'} F :=
  preservesFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F
lemma preservesSmallestFilteredColimits_of_preservesFilteredColimits (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w', w} F] : PreservesFilteredColimitsOfSize.{0, 0} F :=
  preservesFilteredColimitsOfSize_shrink F
end Preserves
section Reflects
@[nolint checkUnivs, pp_with_univ]
class ReflectsFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  reflects_filtered_colimits :
    ∀ (J : Type w) [Category.{w'} J] [IsFiltered J], ReflectsColimitsOfShape J F
abbrev ReflectsFilteredColimits (F : C ⥤ D) : Prop :=
  ReflectsFilteredColimitsOfSize.{v, v} F
attribute [instance 100] ReflectsFilteredColimitsOfSize.reflects_filtered_colimits
instance (priority := 100) ReflectsColimits.reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsColimitsOfSize.{w, w'} F] : ReflectsFilteredColimitsOfSize.{w, w'} F where
  reflects_filtered_colimits _ := inferInstance
instance comp_reflectsFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFilteredColimitsOfSize.{w, w'} F] [ReflectsFilteredColimitsOfSize.{w, w'} G] :
      ReflectsFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_filtered_colimits _ := inferInstance
lemma reflectsFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsFilteredColimitsOfSize.{w', w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w₂} F where
  reflects_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm
    haveI := IsFiltered.of_equivalence e.symm
    exact reflectsColimitsOfShape_of_equiv e F
lemma reflectsFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w'} F :=
  reflectsFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F
lemma reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{w', w} F] : ReflectsFilteredColimitsOfSize.{0, 0} F :=
  reflectsFilteredColimitsOfSize_shrink F
end Reflects
end FilteredColimits
section CofilteredLimits
section Preserves
@[nolint checkUnivs, pp_with_univ]
class PreservesCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  preserves_cofiltered_limits :
    ∀ (J : Type w) [Category.{w'} J] [IsCofiltered J], PreservesLimitsOfShape J F
abbrev PreservesCofilteredLimits (F : C ⥤ D) : Prop :=
  PreservesCofilteredLimitsOfSize.{v, v} F
attribute [instance 100] PreservesCofilteredLimitsOfSize.preserves_cofiltered_limits
instance (priority := 100) PreservesLimits.preservesCofilteredLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w'} F] : PreservesCofilteredLimitsOfSize.{w, w'} F where
  preserves_cofiltered_limits _ := inferInstance
instance comp_preservesCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesCofilteredLimitsOfSize.{w, w'} F] [PreservesCofilteredLimitsOfSize.{w, w'} G] :
      PreservesCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_cofiltered_limits _ := inferInstance
lemma preservesCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesCofilteredLimitsOfSize.{w', w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w₂} F where
  preserves_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm
    haveI := IsCofiltered.of_equivalence e.symm
    exact preservesLimitsOfShape_of_equiv e F
lemma preservesCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w'} F :=
  preservesCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F
lemma preservesSmallestCofilteredLimits_of_preservesCofilteredLimits (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{w', w} F] : PreservesCofilteredLimitsOfSize.{0, 0} F :=
  preservesCofilteredLimitsOfSize_shrink F
end Preserves
section Reflects
@[nolint checkUnivs, pp_with_univ]
class ReflectsCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  reflects_cofiltered_limits :
    ∀ (J : Type w) [Category.{w'} J] [IsCofiltered J], ReflectsLimitsOfShape J F
abbrev ReflectsCofilteredLimits (F : C ⥤ D) : Prop :=
  ReflectsCofilteredLimitsOfSize.{v, v} F
attribute [instance 100] ReflectsCofilteredLimitsOfSize.reflects_cofiltered_limits
instance (priority := 100) ReflectsLimits.reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsLimitsOfSize.{w, w'} F] : ReflectsCofilteredLimitsOfSize.{w, w'} F where
  reflects_cofiltered_limits _ := inferInstance
instance comp_reflectsCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsCofilteredLimitsOfSize.{w, w'} F] [ReflectsCofilteredLimitsOfSize.{w, w'} G] :
      ReflectsCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_cofiltered_limits _ := inferInstance
lemma reflectsCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsCofilteredLimitsOfSize.{w', w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w₂} F where
  reflects_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm
    haveI := IsCofiltered.of_equivalence e.symm
    exact reflectsLimitsOfShape_of_equiv e F
lemma reflectsCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w'} F :=
  reflectsCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F
lemma reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{w', w} F] : ReflectsCofilteredLimitsOfSize.{0, 0} F :=
  reflectsCofilteredLimitsOfSize_shrink F
end Reflects
end CofilteredLimits
end CategoryTheory.Limits