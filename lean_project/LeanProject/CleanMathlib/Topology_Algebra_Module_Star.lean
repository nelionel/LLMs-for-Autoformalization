import Mathlib.Algebra.Star.Module
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Star
@[inherit_doc]
notation:25 M " →L⋆[" R "] " M₂ => ContinuousLinearMap (starRingEnd R) M M₂
@[inherit_doc]
notation:50 M " ≃L⋆[" R "] " M₂ => ContinuousLinearEquiv (starRingEnd R) M M₂
@[simps!]
def starL (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L⋆[R] A where
  toLinearEquiv := starLinearEquiv R
  continuous_toFun := continuous_star
  continuous_invFun := continuous_star
@[simps!]
def starL' (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [TrivialStar R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A] :
    A ≃L[R] A :=
  (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp [starRingEnd_apply]
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)
variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A] [Invertible (2 : R)] [TopologicalSpace A]
theorem continuous_selfAdjointPart [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (selfAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _
theorem continuous_skewAdjointPart [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (skewAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _
theorem continuous_decomposeProdAdjoint [TopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : Continuous (StarModule.decomposeProdAdjoint R A) :=
  (continuous_selfAdjointPart R A).prod_mk (continuous_skewAdjointPart R A)
theorem continuous_decomposeProdAdjoint_symm [TopologicalAddGroup A] :
    Continuous (StarModule.decomposeProdAdjoint R A).symm :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
@[simps!]
def selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] selfAdjoint A where
  toLinearMap := selfAdjointPart R
  cont := continuous_selfAdjointPart _ _
attribute [nolint simpNF] selfAdjointPartL_apply_coe
@[simps!]
def skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] skewAdjoint A where
  toLinearMap := skewAdjointPart R
  cont := continuous_skewAdjointPart _ _
@[simps!]
def StarModule.decomposeProdAdjointL [TopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A where
  toLinearEquiv := StarModule.decomposeProdAdjoint R A
  continuous_toFun := continuous_decomposeProdAdjoint _ _
  continuous_invFun := continuous_decomposeProdAdjoint_symm _ _