import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic
noncomputable section
open RCLike
open scoped ComplexConjugate Classical
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y
namespace LinearPMap
def IsFormalAdjoint (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] E) : Prop :=
  ∀ (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫
variable {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
@[symm]
protected theorem IsFormalAdjoint.symm (h : T.IsFormalAdjoint S) :
    S.IsFormalAdjoint T := fun y _ => by
  rw [← inner_conj_symm, ← inner_conj_symm (y : F), h]
variable (T)
def adjointDomain : Submodule 𝕜 F where
  carrier := {y | Continuous ((innerₛₗ 𝕜 y).comp T.toFun)}
  zero_mem' := by
    rw [Set.mem_setOf_eq, LinearMap.map_zero, LinearMap.zero_comp]
    exact continuous_zero
  add_mem' hx hy := by rw [Set.mem_setOf_eq, LinearMap.map_add] at *; exact hx.add hy
  smul_mem' a x hx := by
    rw [Set.mem_setOf_eq, LinearMap.map_smulₛₗ] at *
    exact hx.const_smul (conj a)
def adjointDomainMkCLM (y : T.adjointDomain) : T.domain →L[𝕜] 𝕜 :=
  ⟨(innerₛₗ 𝕜 (y : F)).comp T.toFun, y.prop⟩
theorem adjointDomainMkCLM_apply (y : T.adjointDomain) (x : T.domain) :
    adjointDomainMkCLM T y x = ⟪(y : F), T x⟫ :=
  rfl
variable {T}
variable (hT : Dense (T.domain : Set E))
def adjointDomainMkCLMExtend (y : T.adjointDomain) : E →L[𝕜] 𝕜 :=
  (T.adjointDomainMkCLM y).extend (Submodule.subtypeL T.domain) hT.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing
@[simp]
theorem adjointDomainMkCLMExtend_apply (y : T.adjointDomain) (x : T.domain) :
    adjointDomainMkCLMExtend hT y (x : E) = ⟪(y : F), T x⟫ :=
  ContinuousLinearMap.extend_eq _ _ _ _ _
variable [CompleteSpace E]
def adjointAux : T.adjointDomain →ₗ[𝕜] E where
  toFun y := (InnerProductSpace.toDual 𝕜 E).symm (adjointDomainMkCLMExtend hT y)
  map_add' x y :=
    hT.eq_of_inner_left fun _ => by
      simp only [inner_add_left, Submodule.coe_add, InnerProductSpace.toDual_symm_apply,
        adjointDomainMkCLMExtend_apply]
  map_smul' _ _ :=
    hT.eq_of_inner_left fun _ => by
      simp only [inner_smul_left, Submodule.coe_smul_of_tower, RingHom.id_apply,
        InnerProductSpace.toDual_symm_apply, adjointDomainMkCLMExtend_apply]
theorem adjointAux_inner (y : T.adjointDomain) (x : T.domain) :
    ⟪adjointAux hT y, x⟫ = ⟪(y : F), T x⟫ := by
  simp only [adjointAux, LinearMap.coe_mk, InnerProductSpace.toDual_symm_apply,
    adjointDomainMkCLMExtend_apply]
  simp only [AddHom.coe_mk, InnerProductSpace.toDual_symm_apply]
  rw [adjointDomainMkCLMExtend_apply]
theorem adjointAux_unique (y : T.adjointDomain) {x₀ : E}
    (hx₀ : ∀ x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : adjointAux hT y = x₀ :=
  hT.eq_of_inner_left fun v => (adjointAux_inner hT _ _).trans (hx₀ v).symm
variable (T)
def adjoint : F →ₗ.[𝕜] E where
  domain := T.adjointDomain
  toFun := if hT : Dense (T.domain : Set E) then adjointAux hT else 0
scoped postfix:1024 "†" => LinearPMap.adjoint
theorem mem_adjoint_domain_iff (y : F) : y ∈ T†.domain ↔ Continuous ((innerₛₗ 𝕜 y).comp T.toFun) :=
  Iff.rfl
variable {T}
theorem mem_adjoint_domain_of_exists (y : F) (h : ∃ w : E, ∀ x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫) :
    y ∈ T†.domain := by
  cases' h with w hw
  rw [T.mem_adjoint_domain_iff]
  have : Continuous ((innerSL 𝕜 w).comp T.domain.subtypeL) := by fun_prop
  convert this using 1
  exact funext fun x => (hw x).symm
theorem adjoint_apply_of_not_dense (hT : ¬Dense (T.domain : Set E)) (y : T†.domain) : T† y = 0 := by
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, not_false_iff, dif_neg, LinearMap.zero_apply]
theorem adjoint_apply_of_dense (y : T†.domain) : T† y = adjointAux hT y := by
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, dif_pos, LinearMap.coe_mk]
include hT in
theorem adjoint_apply_eq (y : T†.domain) {x₀ : E} (hx₀ : ∀ x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) :
    T† y = x₀ :=
  (adjoint_apply_of_dense hT y).symm ▸ adjointAux_unique hT _ hx₀
include hT in
theorem adjoint_isFormalAdjoint : T†.IsFormalAdjoint T := fun x =>
  (adjoint_apply_of_dense hT x).symm ▸ adjointAux_inner hT x
include hT in
theorem IsFormalAdjoint.le_adjoint (h : T.IsFormalAdjoint S) : S ≤ T† :=
  ⟨
  fun x hx =>
    mem_adjoint_domain_of_exists _
      ⟨S ⟨x, hx⟩, h.symm ⟨x, hx⟩⟩,
  fun _ _ hxy => (adjoint_apply_eq hT _ fun _ => by rw [h.symm, hxy]).symm⟩
end LinearPMap
namespace ContinuousLinearMap
variable [CompleteSpace E] [CompleteSpace F]
variable (A : E →L[𝕜] F) {p : Submodule 𝕜 E}
theorem toPMap_adjoint_eq_adjoint_toPMap_of_dense (hp : Dense (p : Set E)) :
    (A.toPMap p).adjoint = A.adjoint.toPMap ⊤ := by
  ext x y hxy
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, iff_true,
      LinearPMap.mem_adjoint_domain_iff, LinearMap.coe_comp, innerₛₗ_apply_coe]
    exact ((innerSL 𝕜 x).comp <| A.comp <| Submodule.subtypeL _).cont
  refine LinearPMap.adjoint_apply_eq ?_ _ fun v => ?_
  · 
    simpa using hp
  · simp only [adjoint_inner_left, hxy, LinearMap.toPMap_apply, coe_coe]
end ContinuousLinearMap
section Star
namespace LinearPMap
variable [CompleteSpace E]
instance instStar : Star (E →ₗ.[𝕜] E) where
  star := fun A ↦ A.adjoint
variable {A : E →ₗ.[𝕜] E}
theorem isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A := Iff.rfl
theorem _root_.IsSelfAdjoint.dense_domain (hA : IsSelfAdjoint A) : Dense (A.domain : Set E) := by
  by_contra h
  rw [isSelfAdjoint_def] at hA
  have h' : A.domain = ⊤ := by
    rw [← hA, Submodule.eq_top_iff']
    intro x
    rw [mem_adjoint_domain_iff, ← hA]
    refine (innerSL 𝕜 x).cont.comp ?_
    simp only [adjoint, h]
    exact continuous_const
  simp [h'] at h
end LinearPMap
end Star