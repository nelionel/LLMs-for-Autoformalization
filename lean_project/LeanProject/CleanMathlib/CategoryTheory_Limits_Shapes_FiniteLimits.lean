import Mathlib.CategoryTheory.FinCategory.AsType
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Data.Fintype.Option
universe w' w v' u' v u
noncomputable section
open CategoryTheory
namespace CategoryTheory.Limits
variable (C : Type u) [Category.{v} C]
class HasFiniteLimits : Prop where
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _
instance (priority := 100) hasLimitsOfShape_of_hasFiniteLimits (J : Type w) [SmallCategory J]
    [FinCategory J] [HasFiniteLimits C] : HasLimitsOfShape J C := by
  apply @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteLimits.out
lemma hasFiniteLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteLimits C where
  out := fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasLimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _
instance (priority := 100) hasFiniteLimits_of_hasLimits [HasLimits C] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C
instance (priority := 90) hasFiniteLimits_of_hasLimitsOfSize₀ [HasLimitsOfSize.{0, 0} C] :
    HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C
theorem hasFiniteLimits_of_hasFiniteLimits_of_size
    (h : ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasLimitsOfShape J C) :
    HasFiniteLimits C where
  out := fun J hJ hhJ => by
    haveI := h (ULiftHom.{w} (ULift.{w} J)) <| @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                          (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasLimitsOfShape_of_equivalence (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) C _ J hJ
      (@Equivalence.symm J hJ (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) l) _
class HasFiniteColimits : Prop where
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _
instance (priority := 100) hasColimitsOfShape_of_hasFiniteColimits (J : Type w) [SmallCategory J]
    [FinCategory J] [HasFiniteColimits C] : HasColimitsOfShape J C := by
  refine @hasColimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteColimits.out
lemma hasFiniteColimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] :
    HasFiniteColimits C where
  out := fun J hJ hJ' =>
    haveI := hasColimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasColimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _
instance (priority := 100) hasFiniteColimits_of_hasColimits [HasColimits C] : HasFiniteColimits C :=
  hasFiniteColimits_of_hasColimitsOfSize C
instance (priority := 90) hasFiniteColimits_of_hasColimitsOfSize₀ [HasColimitsOfSize.{0, 0} C] :
    HasFiniteColimits C :=
  hasFiniteColimits_of_hasColimitsOfSize C
theorem hasFiniteColimits_of_hasFiniteColimits_of_size
    (h : ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasColimitsOfShape J C) :
    HasFiniteColimits C where
  out := fun J hJ hhJ => by
    haveI := h (ULiftHom.{w} (ULift.{w} J)) <| @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                           (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasColimitsOfShape_of_equivalence (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) C _ J hJ
      (@Equivalence.symm J hJ (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) l) _
section
open WalkingParallelPair WalkingParallelPairHom
instance fintypeWalkingParallelPair : Fintype WalkingParallelPair where
  elems := [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete x := by cases x <;> simp
instance instFintypeWalkingParallelPairHom (j j' : WalkingParallelPair) :
    Fintype (WalkingParallelPairHom j j') where
  elems :=
    WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset
        [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by
    rintro (_|_) <;> simp
    cases j <;> simp
end
instance : FinCategory WalkingParallelPair where
  fintypeObj := fintypeWalkingParallelPair
  fintypeHom := instFintypeWalkingParallelPairHom 
example [HasFiniteLimits C] : HasEqualizers C := by infer_instance
example [HasFiniteColimits C] : HasCoequalizers C := by infer_instance
variable {J : Type v}
namespace WidePullbackShape
instance fintypeObj [Fintype J] : Fintype (WidePullbackShape J) :=
  inferInstanceAs <| Fintype (Option _)
instance fintypeHom (j j' : WidePullbackShape J) : Fintype (j ⟶ j') where
  elems := by
    cases' j' with j'
    · cases' j with j
      · exact {Hom.id none}
      · exact {Hom.term j}
    · by_cases h : some j' = j
      · rw [h]
        exact {Hom.id j}
      · exact ∅
  complete := by
    rintro (_|_)
    · cases j <;> simp
    · simp
end WidePullbackShape
namespace WidePushoutShape
instance fintypeObj [Fintype J] : Fintype (WidePushoutShape J) := by
  rw [WidePushoutShape]; infer_instance
instance fintypeHom (j j' : WidePushoutShape J) : Fintype (j ⟶ j') where
  elems := by
    cases' j with j
    · cases' j' with j'
      · exact {Hom.id none}
      · exact {Hom.init j'}
    · by_cases h : some j = j'
      · rw [h]
        exact {Hom.id j'}
      · exact ∅
  complete := by
    rintro (_|_)
    · cases j <;> simp
    · simp
end WidePushoutShape
instance finCategoryWidePullback [Fintype J] : FinCategory (WidePullbackShape J) where
  fintypeHom := WidePullbackShape.fintypeHom
instance finCategoryWidePushout [Fintype J] : FinCategory (WidePushoutShape J) where
  fintypeHom := WidePushoutShape.fintypeHom
class HasFiniteWidePullbacks : Prop where
  out (J : Type) [Finite J] : HasLimitsOfShape (WidePullbackShape J) C
instance hasLimitsOfShape_widePullbackShape (J : Type) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  haveI := @HasFiniteWidePullbacks.out C _ _ J
  infer_instance
class HasFiniteWidePushouts : Prop where
  out (J : Type) [Finite J] : HasColimitsOfShape (WidePushoutShape J) C
instance hasColimitsOfShape_widePushoutShape (J : Type) [Finite J] [HasFiniteWidePushouts C] :
    HasColimitsOfShape (WidePushoutShape J) C := by
  haveI := @HasFiniteWidePushouts.out C _ _ J
  infer_instance
instance (priority := 900) hasFiniteWidePullbacks_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteWidePullbacks C :=
  ⟨fun J _ => by cases nonempty_fintype J; exact HasFiniteLimits.out _⟩
instance (priority := 900) hasFiniteWidePushouts_of_has_finite_limits [HasFiniteColimits C] :
    HasFiniteWidePushouts C :=
  ⟨fun J _ => by cases nonempty_fintype J; exact HasFiniteColimits.out _⟩
instance fintypeWalkingPair : Fintype WalkingPair where
  elems := {WalkingPair.left, WalkingPair.right}
  complete x := by cases x <;> simp
example [HasFiniteWidePullbacks C] : HasPullbacks C := by infer_instance
example [HasFiniteWidePushouts C] : HasPushouts C := by infer_instance
end CategoryTheory.Limits