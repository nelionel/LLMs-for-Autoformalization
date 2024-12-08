import Mathlib.Logic.Small.Set
import Mathlib.CategoryTheory.Filtered.Final
universe w v v₁ u u₁
open CategoryTheory Functor
namespace CategoryTheory
section FinallySmall
variable (J : Type u) [Category.{v} J]
class FinallySmall : Prop where
  final_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Final F
theorem FinallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Final F] : FinallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩
def FinalModel [FinallySmall.{w} J] : Type w :=
  Classical.choose (@FinallySmall.final_smallCategory J _ _)
noncomputable instance smallCategoryFinalModel [FinallySmall.{w} J] :
    SmallCategory (FinalModel J) :=
  Classical.choose (Classical.choose_spec (@FinallySmall.final_smallCategory J _ _))
noncomputable def fromFinalModel [FinallySmall.{w} J] : FinalModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))
instance final_fromFinalModel [FinallySmall.{w} J] : Final (fromFinalModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))
theorem finallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : FinallySmall.{w} J :=
  FinallySmall.mk' (equivSmallModel.{w} J).inverse
variable {J}
variable {K : Type u₁} [Category.{v₁} K]
theorem finallySmall_of_final_of_finallySmall [FinallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  suffices Final ((fromFinalModel K) ⋙ F) from .mk' ((fromFinalModel K) ⋙ F)
  final_comp _ _
theorem finallySmall_of_final_of_essentiallySmall [EssentiallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  have := finallySmall_of_essentiallySmall K
  finallySmall_of_final_of_finallySmall F
end FinallySmall
section InitiallySmall
variable (J : Type u) [Category.{v} J]
class InitiallySmall : Prop where
  initial_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Initial F
theorem InitiallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩
def InitialModel [InitiallySmall.{w} J] : Type w :=
  Classical.choose (@InitiallySmall.initial_smallCategory J _ _)
noncomputable instance smallCategoryInitialModel [InitiallySmall.{w} J] :
    SmallCategory (InitialModel J) :=
  Classical.choose (Classical.choose_spec (@InitiallySmall.initial_smallCategory J _ _))
noncomputable def fromInitialModel [InitiallySmall.{w} J] : InitialModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))
instance initial_fromInitialModel [InitiallySmall.{w} J] : Initial (fromInitialModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))
theorem initiallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : InitiallySmall.{w} J :=
  InitiallySmall.mk' (equivSmallModel.{w} J).inverse
variable {J}
variable {K : Type u₁} [Category.{v₁} K]
theorem initiallySmall_of_initial_of_initiallySmall [InitiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  suffices Initial ((fromInitialModel K) ⋙ F) from .mk' ((fromInitialModel K) ⋙ F)
  initial_comp _ _
theorem initiallySmall_of_initial_of_essentiallySmall [EssentiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  have := initiallySmall_of_essentiallySmall K
  initiallySmall_of_initial_of_initiallySmall F
end InitiallySmall
section WeaklyTerminal
variable (J : Type u) [Category.{v} J]
theorem FinallySmall.exists_small_weakly_terminal_set [FinallySmall.{w} J] :
    ∃ (s : Set J) (_ : Small.{w} s), ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) := by
  refine ⟨Set.range (fromFinalModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (StructuredArrow i (fromFinalModel J)) := IsConnected.is_nonempty
  exact ⟨(fromFinalModel J).obj f.right, Set.mem_range_self _, ⟨f.hom⟩⟩
variable {J} in
theorem finallySmall_of_small_weakly_terminal_set [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j)) : FinallySmall.{v} J := by
  suffices Functor.Final (fullSubcategoryInclusion (· ∈ s)) from
    finallySmall_of_final_of_essentiallySmall (fullSubcategoryInclusion (· ∈ s))
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩
theorem finallySmall_iff_exists_small_weakly_terminal_set [IsFilteredOrEmpty J] :
    FinallySmall.{v} J ↔ ∃ (s : Set J) (_ : Small.{v} s), ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) := by
  refine ⟨fun _ => FinallySmall.exists_small_weakly_terminal_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact finallySmall_of_small_weakly_terminal_set s hs'
end WeaklyTerminal
section WeaklyInitial
variable (J : Type u) [Category.{v} J]
theorem InitiallySmall.exists_small_weakly_initial_set [InitiallySmall.{w} J] :
    ∃ (s : Set J) (_ : Small.{w} s), ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i) := by
  refine ⟨Set.range (fromInitialModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (CostructuredArrow (fromInitialModel J) i) := IsConnected.is_nonempty
  exact ⟨(fromInitialModel J).obj f.left, Set.mem_range_self _, ⟨f.hom⟩⟩
variable {J} in
theorem initiallySmall_of_small_weakly_initial_set [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i)) : InitiallySmall.{v} J := by
  suffices Functor.Initial (fullSubcategoryInclusion (· ∈ s)) from
    initiallySmall_of_initial_of_essentiallySmall (fullSubcategoryInclusion (· ∈ s))
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩
theorem initiallySmall_iff_exists_small_weakly_initial_set [IsCofilteredOrEmpty J] :
    InitiallySmall.{v} J ↔ ∃ (s : Set J) (_ : Small.{v} s), ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i) := by
  refine ⟨fun _ => InitiallySmall.exists_small_weakly_initial_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact initiallySmall_of_small_weakly_initial_set s hs'
end WeaklyInitial
namespace Limits
theorem hasColimitsOfShape_of_finallySmall (J : Type u) [Category.{v} J] [FinallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasColimitsOfSize.{w, w} C] : HasColimitsOfShape J C :=
  Final.hasColimitsOfShape_of_final (fromFinalModel J)
theorem hasLimitsOfShape_of_initiallySmall (J : Type u) [Category.{v} J] [InitiallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasLimitsOfSize.{w, w} C] : HasLimitsOfShape J C :=
  Initial.hasLimitsOfShape_of_initial (fromInitialModel J)
end Limits
end CategoryTheory