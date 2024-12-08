import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
suppress_compilation
open Metric
open scoped NNReal Topology Uniformity
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
section SemiNormed
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
namespace ContinuousLinearMap
section MultiplicationLinear
section NonUnital
variable (𝕜) (𝕜' : Type*) [NonUnitalSeminormedRing 𝕜']
variable [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜']
def mul : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  (LinearMap.mul 𝕜 𝕜').mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y
@[simp]
theorem mul_apply' (x y : 𝕜') : mul 𝕜 𝕜' x y = x * y :=
  rfl
@[simp]
theorem opNorm_mul_apply_le (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)
@[deprecated (since := "2024-02-02")] alias op_norm_mul_apply_le := opNorm_mul_apply_le
theorem opNorm_mul_le : ‖mul 𝕜 𝕜'‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
@[deprecated (since := "2024-02-02")] alias op_norm_mul_le := opNorm_mul_le
def _root_.NonUnitalAlgHom.Lmul : 𝕜' →ₙₐ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  { mul 𝕜 𝕜' with
    map_mul' := fun _ _ ↦ ext fun _ ↦ mul_assoc _ _ _
    map_zero' := ext fun _ ↦ zero_mul _ }
variable {𝕜 𝕜'} in
@[simp]
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl
def mulLeftRight : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  ((compL 𝕜 𝕜' 𝕜' 𝕜').comp (mul 𝕜 𝕜').flip).flip.comp (mul 𝕜 𝕜')
@[simp]
theorem mulLeftRight_apply (x y z : 𝕜') : mulLeftRight 𝕜 𝕜' x y z = x * z * y :=
  rfl
theorem opNorm_mulLeftRight_apply_apply_le (x y : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x y‖ ≤ ‖x‖ * ‖y‖ :=
  (opNorm_comp_le _ _).trans <|
    (mul_comm _ _).trans_le <|
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)
@[deprecated (since := "2024-02-02")]
alias op_norm_mulLeftRight_apply_apply_le :=
  opNorm_mulLeftRight_apply_apply_le
theorem opNorm_mulLeftRight_apply_le (x : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 𝕜' x)
@[deprecated (since := "2024-02-02")]
alias op_norm_mulLeftRight_apply_le := opNorm_mulLeftRight_apply_le
#adaptation_note
set_option maxSynthPendingDepth 2 in
theorem opNorm_mulLeftRight_le :
    ‖mulLeftRight 𝕜 𝕜'‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 𝕜' x
@[deprecated (since := "2024-02-02")] alias op_norm_mulLeftRight_le := opNorm_mulLeftRight_le
class _root_.RegularNormedAlgebra : Prop where
  isometry_mul' : Isometry (mul 𝕜 𝕜')
instance _root_.NormedAlgebra.instRegularNormedAlgebra {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] : RegularNormedAlgebra 𝕜 𝕜' where
  isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 𝕜') <|
    fun x => le_antisymm (opNorm_mul_apply_le _ _ _) <| by
      convert ratio_le_opNorm ((mul 𝕜 𝕜') x) (1 : 𝕜')
      simp [norm_one]
variable [RegularNormedAlgebra 𝕜 𝕜']
lemma isometry_mul : Isometry (mul 𝕜 𝕜') :=
  RegularNormedAlgebra.isometry_mul'
@[simp]
lemma opNorm_mul_apply (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 𝕜')).mp (isometry_mul 𝕜 𝕜') x
@[deprecated (since := "2024-02-02")] alias op_norm_mul_apply := opNorm_mul_apply
@[simp]
lemma opNNNorm_mul_apply (x : 𝕜') : ‖mul 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| opNorm_mul_apply 𝕜 𝕜' x
@[deprecated (since := "2024-02-02")] alias op_nnnorm_mul_apply := opNNNorm_mul_apply
def mulₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' where
  toLinearMap := mul 𝕜 𝕜'
  norm_map' x := opNorm_mul_apply 𝕜 𝕜' x
@[simp]
theorem coe_mulₗᵢ : ⇑(mulₗᵢ 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl
end NonUnital
section RingEquiv
variable (𝕜 E)
def ring_lmap_equiv_selfₗ : (𝕜 →L[𝕜] E) ≃ₗ[𝕜] E where
  toFun := fun f ↦ f 1
  invFun := (ContinuousLinearMap.id 𝕜 𝕜).smulRight
  map_smul' := fun a f ↦ by simp only [coe_smul', Pi.smul_apply, RingHom.id_apply]
  map_add' := fun f g ↦ by simp only [add_apply]
  left_inv := fun f ↦ by ext; simp only [smulRight_apply, coe_id', _root_.id, one_smul]
  right_inv := fun m ↦ by simp only [smulRight_apply, id_apply, one_smul]
def ring_lmap_equiv_self : (𝕜 →L[𝕜] E) ≃ₗᵢ[𝕜] E where
  toLinearEquiv := ring_lmap_equiv_selfₗ 𝕜 E
  norm_map' := by
    refine fun f ↦ le_antisymm ?_ ?_
    · simpa only [norm_one, mul_one] using le_opNorm f 1
    · refine opNorm_le_bound' f (norm_nonneg <| f 1) (fun x _ ↦ ?_)
      rw [(by rw [smul_eq_mul, mul_one] : f x = f (x • 1)), ContinuousLinearMap.map_smul,
        norm_smul, mul_comm, (by rfl : ring_lmap_equiv_selfₗ 𝕜 E f = f 1)]
end RingEquiv
end MultiplicationLinear
section SMulLinear
variable (𝕜) (𝕜' : Type*) [NormedField 𝕜']
variable [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
def lsmul : 𝕜' →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : 𝕜' →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using norm_smul_le c x
@[simp]
theorem lsmul_apply (c : 𝕜') (x : E) : lsmul 𝕜 𝕜' c x = c • x :=
  rfl
variable {𝕜'}
theorem norm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖ = ‖x‖ := by
  refine opNorm_eq_of_bounds (norm_nonneg _) (fun x => ?_) fun N _ h => ?_
  · rw [toSpanSingleton_apply, norm_smul, mul_comm]
  · specialize h 1
    rw [toSpanSingleton_apply, norm_smul, mul_comm] at h
    exact (mul_le_mul_right (by simp)).mp h
variable {𝕜}
theorem opNorm_lsmul_apply_le (x : 𝕜') : ‖(lsmul 𝕜 𝕜' x : E →L[𝕜] E)‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y
@[deprecated (since := "2024-02-02")] alias op_norm_lsmul_apply_le := opNorm_lsmul_apply_le
theorem opNorm_lsmul_le : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp_rw [one_mul]
  exact opNorm_lsmul_apply_le _
@[deprecated (since := "2024-02-02")] alias op_norm_lsmul_le := opNorm_lsmul_le
end SMulLinear
end ContinuousLinearMap
end SemiNormed
section Normed
namespace ContinuousLinearMap
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (𝕜) (𝕜' : Type*)
section
variable [NonUnitalNormedRing 𝕜'] [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
variable [SMulCommClass 𝕜 𝕜' 𝕜'] [RegularNormedAlgebra 𝕜 𝕜'] [Nontrivial 𝕜']
@[simp]
theorem opNorm_mul : ‖mul 𝕜 𝕜'‖ = 1 :=
  (mulₗᵢ 𝕜 𝕜').norm_toContinuousLinearMap
@[deprecated (since := "2024-02-02")] alias op_norm_mul := opNorm_mul
@[simp]
theorem opNNNorm_mul : ‖mul 𝕜 𝕜'‖₊ = 1 :=
  Subtype.ext <| opNorm_mul 𝕜 𝕜'
@[deprecated (since := "2024-02-02")] alias op_nnnorm_mul := opNNNorm_mul
end
@[simp]
theorem opNorm_lsmul [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E]
    [IsScalarTower 𝕜 𝕜' E] [Nontrivial E] : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ = 1 := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => ?_) fun N _ h => ?_
  · rw [one_mul]
    apply opNorm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have := le_of_opNorm_le _ (h 1) y
  simp_rw [lsmul_apply, one_smul, norm_one, mul_one] at this
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simp_rw [one_mul, this]
@[deprecated (since := "2024-02-02")] alias op_norm_lsmul := opNorm_lsmul
end ContinuousLinearMap
end Normed