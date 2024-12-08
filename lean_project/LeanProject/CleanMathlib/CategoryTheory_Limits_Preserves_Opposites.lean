import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Finite
universe w w' v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory
namespace CategoryTheory.Limits
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]
lemma preservesLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.op where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩
lemma preservesLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op] :
    PreservesLimit K F where
  preserves {_} hc := ⟨isLimitOfOp (isColimitOfPreserves F.op (IsLimit.op hc))⟩
lemma preservesLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.leftOp where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩
lemma preservesLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op F.leftOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.leftOp (IsLimit.op hc))⟩
lemma preservesLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] :
    PreservesLimit K F.rightOp where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)⟩
lemma preservesLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.leftOp F.rightOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfOp (isColimitOfPreserves F.rightOp (isColimitCoconeLeftOpOfCone _ hc))⟩
lemma preservesLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] :
    PreservesLimit K F.unop where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)⟩
lemma preservesLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F.unop] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩
lemma preservesColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.op where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩
lemma preservesColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op] :
    PreservesColimit K F where
  preserves {_} hc := ⟨isColimitOfOp (isLimitOfPreserves F.op (IsColimit.op hc))⟩
lemma preservesColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.leftOp where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩
lemma preservesColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op F.leftOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.leftOp (IsColimit.op hc))⟩
lemma preservesColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] :
    PreservesColimit K F.rightOp where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)⟩
lemma preservesColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.leftOp F.rightOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfOp (isLimitOfPreserves F.rightOp (isLimitConeLeftOpOfCocone _ hc))⟩
lemma preservesColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] :
    PreservesColimit K F.unop where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)⟩
lemma preservesColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F.unop] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.unop (isLimitConeLeftOpOfCocone _ hc))⟩
section
variable (J)
lemma preservesLimitsOfShape_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.op where preservesLimit {K} := preservesLimit_op K F
lemma preservesLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.leftOp where preservesLimit {K} := preservesLimit_leftOp K F
lemma preservesLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.rightOp where preservesLimit {K} := preservesLimit_rightOp K F
lemma preservesLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.unop where preservesLimit {K} := preservesLimit_unop K F
lemma preservesColimitsOfShape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.op where preservesColimit {K} := preservesColimit_op K F
lemma preservesColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.leftOp where preservesColimit {K} := preservesColimit_leftOp K F
lemma preservesColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.rightOp where preservesColimit {K} := preservesColimit_rightOp K F
lemma preservesColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.unop where preservesColimit {K} := preservesColimit_unop K F
lemma preservesLimitsOfShape_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_op K F
lemma preservesLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_leftOp K F
lemma preservesLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_rightOp K F
lemma preservesLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_unop K F
lemma preservesColimitsOfShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_op K F
lemma preservesColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_leftOp K F
lemma preservesColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_rightOp K F
lemma preservesColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_unop K F
end
lemma preservesLimitsOfSize_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _
lemma preservesLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _
lemma preservesLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _
lemma preservesLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _
lemma preservesColimitsOfSize_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _
lemma preservesColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _
lemma preservesColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _
lemma preservesColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _
lemma preservesLimitsOfSize_of_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F.op] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _
lemma preservesLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.leftOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _
lemma preservesLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F.rightOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _
lemma preservesLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.unop] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _
lemma preservesColimitsOfSize_of_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F.op] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _
lemma preservesColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.leftOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _
lemma preservesColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F.rightOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _
lemma preservesColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.unop] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _
lemma preservesLimits_op (F : C ⥤ D) [PreservesColimits F] : PreservesLimits F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _
lemma preservesLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _
lemma preservesLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F] : PreservesLimits F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _
lemma preservesLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _
lemma perservesColimits_op (F : C ⥤ D) [PreservesLimits F] : PreservesColimits F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _
lemma preservesColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _
lemma preservesColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F] :
    PreservesColimits F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _
lemma preservesColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _
lemma preservesLimits_of_op (F : C ⥤ D) [PreservesColimits F.op] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _
lemma preservesLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _
lemma preservesLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp] :
    PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _
lemma preservesLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _
lemma preservesColimits_of_op (F : C ⥤ D) [PreservesLimits F.op] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _
lemma preservesColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _
lemma preservesColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _
lemma preservesColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _
lemma preservesFiniteLimits_op (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.op where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_op J F
lemma preservesFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.leftOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_leftOp J F
lemma preservesFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.rightOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_rightOp J F
lemma preservesFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.unop where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_unop J F
lemma preservesFiniteColimits_op (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.op where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_op J F
lemma preservesFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.leftOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_leftOp J F
lemma preservesFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.rightOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_rightOp J F
lemma preservesFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.unop where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_unop J F
lemma preservesFiniteLimits_of_op (F : C ⥤ D) [PreservesFiniteColimits F.op] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_op J F
lemma preservesFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F.leftOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_leftOp J F
lemma preservesFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F.rightOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_rightOp J F
lemma preservesFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F.unop] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_unop J F
lemma preservesFiniteColimits_of_op (F : C ⥤ D) [PreservesFiniteLimits F.op] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_op J F
lemma preservesFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F.leftOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_leftOp J F
lemma preservesFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F.rightOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_rightOp J F
lemma preservesFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F.unop] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_unop J F
lemma preservesFiniteProducts_op (F : C ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.op where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_op
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite J).symm _
lemma preservesFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.leftOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_leftOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite J).symm _
lemma preservesFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.rightOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_rightOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite J).symm _
lemma preservesFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.unop where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_unop
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite J).symm _
lemma preservesFiniteCoproducts_op (F : C ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.op where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_op
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite J).symm _
lemma preservesFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.leftOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_leftOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite J).symm _
lemma preservesFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.rightOp where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_rightOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite J).symm _
lemma preservesFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.unop where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_unop
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite J).symm _
end CategoryTheory.Limits