import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.UniformSpace.Matrix
open scoped Matrix
variable {𝕜 m n l E : Type*}
section EntrywiseSupNorm
variable [RCLike 𝕜] [Fintype n] [DecidableEq n]
theorem entry_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ ≤ 1 := by
  have norm_sum : ‖U i j‖ ^ 2 ≤ ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      cases' h_x with a h_a
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multiset.mem_map]
      use j
      simp only [eq_self_iff_true, Finset.mem_univ_val, and_self_iff, sq_eq_sq₀]
  have diag_eq_norm_sum : (U * Uᴴ) i i = (∑ x : n, ‖U i x‖ ^ 2 : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply, RCLike.mul_conj,
      RCLike.normSq_eq_def', RCLike.ofReal_pow]; norm_cast
  have re_diag_eq_norm_sum : RCLike.re ((U * Uᴴ) i i) = ∑ x : n, ‖U i x‖ ^ 2 := by
    rw [RCLike.ext_iff] at diag_eq_norm_sum
    rw [diag_eq_norm_sum.1]
    norm_cast
  have mul_eq_one : U * Uᴴ = 1 := unitary.mul_star_self_of_mem hU
  have diag_eq_one : RCLike.re ((U * Uᴴ) i i) = 1 := by
    simp only [mul_eq_one, eq_self_iff_true, Matrix.one_apply_eq, RCLike.one_re]
  rw [← sq_le_one_iff₀ (norm_nonneg (U i j)), ← diag_eq_one, re_diag_eq_norm_sum]
  exact norm_sum
attribute [local instance] Matrix.normedAddCommGroup
theorem entrywise_sup_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    ‖U‖ ≤ 1 := by
  conv => 
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intros
  exact entry_norm_bound_of_unitary hU _ _
end EntrywiseSupNorm
noncomputable section L2OpNorm
namespace Matrix
open LinearMap
variable [RCLike 𝕜]
variable [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l]
def toEuclideanCLM :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :=
  toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜) |>.symm.trans <|
    { toContinuousLinearMap with
      map_mul' := fun _ _ ↦ rfl
      map_star' := adjoint_toContinuousLinearMap }
lemma coe_toEuclideanCLM_eq_toEuclideanLin (A : Matrix n n 𝕜) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) A : _ →ₗ[𝕜] _) = toEuclideanLin A :=
  rfl
@[simp]
lemma toEuclideanCLM_piLp_equiv_symm (A : Matrix n n 𝕜) (x : n → 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) A ((WithLp.equiv _ _).symm x) =
      (WithLp.equiv _ _).symm (toLin' A x) :=
  rfl
@[simp]
lemma piLp_equiv_toEuclideanCLM (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    WithLp.equiv _ _ (toEuclideanCLM (n := n) (𝕜 := 𝕜) A x) =
      toLin' A (WithLp.equiv _ _ x) :=
  rfl
def l2OpNormedAddCommGroupAux : NormedAddCommGroup (Matrix m n 𝕜) :=
  @NormedAddCommGroup.induced ((Matrix m n 𝕜) ≃ₗ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m)) _
    _ _ _ ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup _ _ <|
    (toEuclideanLin.trans toContinuousLinearMap).injective
def l2OpNormedRingAux : NormedRing (Matrix n n 𝕜) :=
  @NormedRing.induced ((Matrix n n 𝕜) ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)) _
    _ _ _ ContinuousLinearMap.toNormedRing _ _ toEuclideanCLM.injective
open Bornology Filter
open scoped Topology Uniformity
def instL2OpMetricSpace : MetricSpace (Matrix m n 𝕜) := by
  letI normed_add_comm_group : NormedAddCommGroup (Matrix m n 𝕜) :=
    { l2OpNormedAddCommGroupAux.replaceTopology <|
        (toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap
        |>.toContinuousLinearEquiv.toHomeomorph.isInducing.eq_induced with
      norm := l2OpNormedAddCommGroupAux.norm
      dist_eq := l2OpNormedAddCommGroupAux.dist_eq }
  exact normed_add_comm_group.replaceUniformity <| by
    congr
    rw [← @UniformAddGroup.toUniformSpace_eq _ (Matrix.instUniformSpace m n 𝕜) _ _]
    rw [@UniformAddGroup.toUniformSpace_eq _ PseudoEMetricSpace.toUniformSpace _ _]
scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpMetricSpace
open scoped Matrix.L2OpNorm
def instL2OpNormedAddCommGroup : NormedAddCommGroup (Matrix m n 𝕜) where
  norm := l2OpNormedAddCommGroupAux.norm
  dist_eq := l2OpNormedAddCommGroupAux.dist_eq
scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedAddCommGroup
lemma l2_opNorm_def (A : Matrix m n 𝕜) :
    ‖A‖ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖ := rfl
@[deprecated (since := "2024-02-02")] alias l2_op_norm_def := l2_opNorm_def
lemma l2_opNNNorm_def (A : Matrix m n 𝕜) :
    ‖A‖₊ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖₊ := rfl
@[deprecated (since := "2024-02-02")] alias l2_op_nnnorm_def := l2_opNNNorm_def
lemma l2_opNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖ = ‖A‖ := by
  rw [l2_opNorm_def, toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    toLin_conjTranspose, adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _
@[deprecated (since := "2024-02-02")] alias l2_op_norm_conjTranspose := l2_opNorm_conjTranspose
lemma l2_opNNNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖₊ = ‖A‖₊ :=
  Subtype.ext <| l2_opNorm_conjTranspose _
@[deprecated (since := "2024-02-02")] alias l2_op_nnnorm_conjTranspose := l2_opNNNorm_conjTranspose
lemma l2_opNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖ = ‖A‖ * ‖A‖ := by
  classical
  rw [l2_opNorm_def, toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun m 𝕜).toBasis), toLin_conjTranspose]
  exact ContinuousLinearMap.norm_adjoint_comp_self _
@[deprecated (since := "2024-02-02")]
alias l2_op_norm_conjTranspose_mul_self := l2_opNorm_conjTranspose_mul_self
lemma l2_opNNNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖₊ = ‖A‖₊ * ‖A‖₊ :=
  Subtype.ext <| l2_opNorm_conjTranspose_mul_self _
@[deprecated (since := "2024-02-02")]
alias l2_op_nnnorm_conjTranspose_mul_self := l2_opNNNorm_conjTranspose_mul_self
lemma l2_opNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(EuclideanSpace.equiv m 𝕜).symm <| A *ᵥ x‖ ≤ ‖A‖ * ‖x‖ :=
  toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) |>.trans toContinuousLinearMap A |>.le_opNorm x
@[deprecated (since := "2024-02-02")] alias l2_op_norm_mulVec := l2_opNorm_mulVec
lemma l2_opNNNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(EuclideanSpace.equiv m 𝕜).symm <| A *ᵥ x‖₊ ≤ ‖A‖₊ * ‖x‖₊ :=
  A.l2_opNorm_mulVec x
@[deprecated (since := "2024-02-02")] alias l2_op_nnnorm_mulVec := l2_opNNNorm_mulVec
lemma l2_opNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  simp only [l2_opNorm_def]
  have := (toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) A
    |>.opNorm_comp_le <| (toEuclideanLin (n := l) (m := n) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) B
  convert this
  ext1 x
  exact congr($(Matrix.toLin'_mul A B) x)
@[deprecated (since := "2024-02-02")] alias l2_op_norm_mul := l2_opNorm_mul
lemma l2_opNNNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ :=
  l2_opNorm_mul A B
@[deprecated (since := "2024-02-02")] alias l2_op_nnnorm_mul := l2_opNNNorm_mul
def instL2OpNormedSpace : NormedSpace 𝕜 (Matrix m n 𝕜) where
  norm_smul_le r x := by
    rw [l2_opNorm_def, LinearEquiv.map_smul]
    exact norm_smul_le r ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x)
scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedSpace
def instL2OpNormedRing : NormedRing (Matrix n n 𝕜) where
  dist_eq := l2OpNormedRingAux.dist_eq
  norm_mul := l2OpNormedRingAux.norm_mul
scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedRing
lemma cstar_norm_def (A : Matrix n n 𝕜) : ‖A‖ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ := rfl
lemma cstar_nnnorm_def (A : Matrix n n 𝕜) : ‖A‖₊ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖₊ := rfl
def instL2OpNormedAlgebra : NormedAlgebra 𝕜 (Matrix n n 𝕜) where
  norm_smul_le := norm_smul_le
scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedAlgebra
lemma instCStarRing : CStarRing (Matrix n n 𝕜) where
  norm_mul_self_le M := le_of_eq <| Eq.symm <| l2_opNorm_conjTranspose_mul_self M
scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instCStarRing
end Matrix
end L2OpNorm