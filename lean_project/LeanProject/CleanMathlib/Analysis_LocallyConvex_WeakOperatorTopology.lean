import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
open Topology
@[irreducible]
def ContinuousLinearMapWOT (𝕜 : Type*) (E : Type*) (F : Type*) [Semiring 𝕜] [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜 E] [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F] :=
  E →L[𝕜] F
@[inherit_doc]
notation:25 E " →WOT[" 𝕜 "] " F => ContinuousLinearMapWOT 𝕜 E F
namespace ContinuousLinearMapWOT
variable {𝕜 : Type*} {E : Type*} {F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
local notation X "⋆" => X →L[𝕜] 𝕜
section Basic
unseal ContinuousLinearMapWOT in
instance instAddCommGroup [TopologicalAddGroup F] : AddCommGroup (E →WOT[𝕜] F) :=
  inferInstanceAs <| AddCommGroup (E →L[𝕜] F)
unseal ContinuousLinearMapWOT in
instance instModule [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] : Module 𝕜 (E →WOT[𝕜] F) :=
  inferInstanceAs <| Module 𝕜 (E →L[𝕜] F)
variable (𝕜) (E) (F) [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
unseal ContinuousLinearMapWOT in
def _root_.ContinuousLinearMap.toWOT :
    (E →L[𝕜] F) ≃ₗ[𝕜] (E →WOT[𝕜] F) :=
  LinearEquiv.refl 𝕜 _
variable {𝕜} {E} {F}
instance instFunLike : FunLike (E →WOT[𝕜] F) E F where
  coe f :=  ((ContinuousLinearMap.toWOT 𝕜 E F).symm f : E → F)
  coe_injective' := by intro; simp
instance instContinuousLinearMapClass : ContinuousLinearMapClass (E →WOT[𝕜] F) 𝕜 E F where
  map_add f x y := by simp only [DFunLike.coe]; simp
  map_smulₛₗ f r x := by simp only [DFunLike.coe]; simp
  map_continuous f := ContinuousLinearMap.continuous ((ContinuousLinearMap.toWOT 𝕜 E F).symm f)
lemma _root_.ContinuousLinearMap.toWOT_apply {A : E →L[𝕜] F} {x : E} :
    ((ContinuousLinearMap.toWOT 𝕜 E F) A) x = A x := rfl
unseal ContinuousLinearMapWOT in
lemma ext {A B : E →WOT[𝕜] F} (h : ∀ x, A x = B x) : A = B := ContinuousLinearMap.ext h
unseal ContinuousLinearMapWOT in
lemma ext_iff {A B : E →WOT[𝕜] F} : A = B ↔ ∀ x, A x = B x := ContinuousLinearMap.ext_iff
@[ext 900]
lemma ext_dual [H : SeparatingDual 𝕜 F] {A B : E →WOT[𝕜] F}
    (h : ∀ x (y : F⋆), y (A x) = y (B x)) : A = B := by
  simp_rw [ext_iff, ← (separatingDual_iff_injective.mp H).eq_iff, LinearMap.ext_iff]
  exact h
@[simp] lemma zero_apply (x : E) : (0 : E →WOT[𝕜] F) x = 0 := by simp only [DFunLike.coe]; rfl
unseal ContinuousLinearMapWOT in
@[simp] lemma add_apply {f g : E →WOT[𝕜] F} (x : E) : (f + g) x = f x + g x := by
  simp only [DFunLike.coe]; rfl
unseal ContinuousLinearMapWOT in
@[simp] lemma sub_apply {f g : E →WOT[𝕜] F} (x : E) : (f - g) x = f x - g x := by
  simp only [DFunLike.coe]; rfl
unseal ContinuousLinearMapWOT in
@[simp] lemma neg_apply {f : E →WOT[𝕜] F} (x : E) : (-f) x = -(f x) := by
  simp only [DFunLike.coe]; rfl
unseal ContinuousLinearMapWOT in
@[simp] lemma smul_apply {f : E →WOT[𝕜] F} (c : 𝕜) (x : E) : (c • f) x = c • (f x) := by
  simp only [DFunLike.coe]; rfl
end Basic
section Topology
variable [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
variable (𝕜) (E) (F) in
def inducingFn : (E →WOT[𝕜] F) →ₗ[𝕜] (E × F⋆ → 𝕜) where
  toFun := fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp
@[simp]
lemma inducingFn_apply {f : E →WOT[𝕜] F} {x : E} {y : F⋆} :
    inducingFn 𝕜 E F f (x, y) = y (f x) :=
  rfl
instance instTopologicalSpace : TopologicalSpace (E →WOT[𝕜] F) :=
  .induced (inducingFn _ _ _) Pi.topologicalSpace
@[fun_prop]
lemma continuous_inducingFn : Continuous (inducingFn 𝕜 E F) :=
  continuous_induced_dom
lemma continuous_dual_apply (x : E) (y : F⋆) : Continuous fun (A : E →WOT[𝕜] F) => y (A x) := by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩
@[fun_prop]
lemma continuous_of_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α → E →WOT[𝕜] F}
    (h : ∀ x (y : F⋆), Continuous fun a => y (g a x)) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)
lemma isInducing_inducingFn : IsInducing (inducingFn 𝕜 E F) := ⟨rfl⟩
lemma isEmbedding_inducingFn [SeparatingDual 𝕜 F] : IsEmbedding (inducingFn 𝕜 E F) := by
  refine Function.Injective.isEmbedding_induced fun A B hAB => ?_
  rw [ContinuousLinearMapWOT.ext_dual_iff]
  simpa [funext_iff] using hAB
@[deprecated (since := "2024-10-26")]
alias embedding_inducingFn := isEmbedding_inducingFn
open Filter in
lemma tendsto_iff_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α → E →WOT[𝕜] F}
    {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x (y : F⋆), Tendsto (fun a => y (f a x)) l (𝓝 (y (A x))) := by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]
lemma le_nhds_iff_forall_dual_apply_le_nhds {l : Filter (E →WOT[𝕜] F)} {A : E →WOT[𝕜] F} :
    l ≤ 𝓝 A ↔ ∀ x (y : F⋆), l.map (fun T => y (T x)) ≤ 𝓝 (y (A x)) :=
  tendsto_iff_forall_dual_apply_tendsto (f := id)
instance instT3Space [SeparatingDual 𝕜 F] : T3Space (E →WOT[𝕜] F) := isEmbedding_inducingFn.t3Space
instance instContinuousAdd : ContinuousAdd (E →WOT[𝕜] F) := .induced (inducingFn 𝕜 E F)
instance instContinuousNeg : ContinuousNeg (E →WOT[𝕜] F) := .induced (inducingFn 𝕜 E F)
instance instContinuousSMul : ContinuousSMul 𝕜 (E →WOT[𝕜] F) := .induced (inducingFn 𝕜 E F)
instance instTopologicalAddGroup : TopologicalAddGroup (E →WOT[𝕜] F) where
instance instUniformSpace : UniformSpace (E →WOT[𝕜] F) := .comap (inducingFn 𝕜 E F) inferInstance
instance instUniformAddGroup : UniformAddGroup (E →WOT[𝕜] F) := .comap (inducingFn 𝕜 E F)
end Topology
section Seminorms
variable [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
def seminorm (x : E) (y : F⋆) : Seminorm 𝕜 (E →WOT[𝕜] F) where
  toFun A := ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp
variable (𝕜) (E) (F) in
def seminormFamily : SeminormFamily 𝕜 (E →WOT[𝕜] F) (E × F⋆) :=
  fun ⟨x, y⟩ => seminorm x y
lemma withSeminorms : WithSeminorms (seminormFamily 𝕜 E F) :=
  let e : E × F⋆ ≃ (Σ _ : E × F⋆, Fin 1) := .symm <| .sigmaUnique _ _
  have : Nonempty (Σ _ : E × F⋆, Fin 1) := e.symm.nonempty
  isInducing_inducingFn.withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜 𝕜)
    |>.congr_equiv e
lemma hasBasis_seminorms : (𝓝 (0 : E →WOT[𝕜] F)).HasBasis (seminormFamily 𝕜 E F).basisSets id :=
  withSeminorms.hasBasis
instance instLocallyConvexSpace [NormedSpace ℝ 𝕜] [Module ℝ (E →WOT[𝕜] F)]
    [IsScalarTower ℝ 𝕜 (E →WOT[𝕜] F)] :
    LocallyConvexSpace ℝ (E →WOT[𝕜] F) :=
  withSeminorms.toLocallyConvexSpace
end Seminorms
section toWOT_continuous
variable [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [ContinuousSMul 𝕜 E]
@[continuity, fun_prop]
lemma ContinuousLinearMap.continuous_toWOT :
    Continuous (ContinuousLinearMap.toWOT 𝕜 E F) :=
  ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y ↦
    y.cont.comp <| continuous_eval_const x
def ContinuousLinearMap.toWOTCLM : (E →L[𝕜] F) →L[𝕜] (E →WOT[𝕜] F) :=
  ⟨LinearEquiv.toLinearMap (ContinuousLinearMap.toWOT 𝕜 E F), ContinuousLinearMap.continuous_toWOT⟩
end toWOT_continuous
end ContinuousLinearMapWOT