import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
noncomputable section
open scoped NNReal Matrix
namespace Matrix
variable {R l m n α β ι : Type*} [Fintype l] [Fintype m] [Fintype n] [Unique ι]
section LinfLinf
section SeminormedAddCommGroup
variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
protected def seminormedAddCommGroup : SeminormedAddCommGroup (Matrix m n α) :=
  Pi.seminormedAddCommGroup
attribute [local instance] Matrix.seminormedAddCommGroup
theorem norm_def (A : Matrix m n α) : ‖A‖ = ‖fun i j => A i j‖ := rfl
lemma norm_eq_sup_sup_nnnorm (A : Matrix m n α) :
    ‖A‖ = Finset.sup Finset.univ fun i ↦ Finset.sup Finset.univ fun j ↦ ‖A i j‖₊ := by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]
theorem nnnorm_def (A : Matrix m n α) : ‖A‖₊ = ‖fun i j => A i j‖₊ := rfl
theorem norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : Matrix m n α} : ‖A‖ ≤ r ↔ ∀ i j, ‖A i j‖ ≤ r := by
  simp_rw [norm_def, pi_norm_le_iff_of_nonneg hr]
theorem nnnorm_le_iff {r : ℝ≥0} {A : Matrix m n α} : ‖A‖₊ ≤ r ↔ ∀ i j, ‖A i j‖₊ ≤ r := by
  simp_rw [nnnorm_def, pi_nnnorm_le_iff]
theorem norm_lt_iff {r : ℝ} (hr : 0 < r) {A : Matrix m n α} : ‖A‖ < r ↔ ∀ i j, ‖A i j‖ < r := by
  simp_rw [norm_def, pi_norm_lt_iff hr]
theorem nnnorm_lt_iff {r : ℝ≥0} (hr : 0 < r) {A : Matrix m n α} :
    ‖A‖₊ < r ↔ ∀ i j, ‖A i j‖₊ < r := by
  simp_rw [nnnorm_def, pi_nnnorm_lt_iff hr]
theorem norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖ ≤ ‖A‖ :=
  (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
theorem nnnorm_entry_le_entrywise_sup_nnnorm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖₊ ≤ ‖A‖₊ :=
  (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)
@[simp]
theorem nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by
  simp only [nnnorm_def, Pi.nnnorm_def, Matrix.map_apply, hf]
@[simp]
theorem norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) : ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_map_eq A f fun a => Subtype.ext <| hf a : _)
@[simp]
theorem nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ :=
  Finset.sup_comm _ _ _
@[simp]
theorem norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_transpose A
@[simp]
theorem nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose
@[simp]
theorem norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_conjTranspose A
instance [StarAddMonoid α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α) :=
  ⟨norm_conjTranspose⟩
@[simp]
theorem nnnorm_col (v : m → α) : ‖col ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]
@[simp]
theorem norm_col (v : m → α) : ‖col ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_col v
@[simp]
theorem nnnorm_row (v : n → α) : ‖row ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]
@[simp]
theorem norm_row (v : n → α) : ‖row ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_row v
@[simp]
theorem nnnorm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  simp_rw [nnnorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine le_antisymm (Finset.sup_le fun j hj => ?_) ?_
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, nnnorm_zero]
      exact zero_le _
  · refine Eq.trans_le ?_ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]
@[simp]
theorem norm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_diagonal v
instance [Nonempty n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α) :=
  ⟨(norm_diagonal _).trans <| norm_one⟩
end SeminormedAddCommGroup
protected def normedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  Pi.normedAddCommGroup
section NormedSpace
attribute [local instance] Matrix.seminormedAddCommGroup
protected theorem boundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [BoundedSMul R α] : BoundedSMul R (Matrix m n α) :=
  Pi.instBoundedSMul
variable [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]
protected def normedSpace : NormedSpace R (Matrix m n α) :=
  Pi.normedSpace
end NormedSpace
end LinfLinf
section LinftyOp
@[local instance]
protected def linftyOpSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : SeminormedAddCommGroup (m → PiLp 1 fun j : n => α))
@[local instance]
protected def linftyOpNormedAddCommGroup [NormedAddCommGroup α] :
    NormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : NormedAddCommGroup (m → PiLp 1 fun j : n => α))
@[local instance]
protected theorem linftyOpBoundedSMul
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [BoundedSMul R α] :
    BoundedSMul R (Matrix m n α) :=
  (by infer_instance : BoundedSMul R (m → PiLp 1 fun j : n => α))
@[local instance]
protected def linftyOpNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  (by infer_instance : NormedSpace R (m → PiLp 1 fun j : n => α))
section SeminormedAddCommGroup
variable [SeminormedAddCommGroup α]
theorem linfty_opNorm_def (A : Matrix m n α) :
    ‖A‖ = ((Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ : ℝ≥0) := by
  change ‖fun i => (WithLp.equiv 1 _).symm (A i)‖ = _
  simp [Pi.norm_def, PiLp.nnnorm_eq_sum ENNReal.one_ne_top]
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_def := linfty_opNorm_def
theorem linfty_opNNNorm_def (A : Matrix m n α) :
    ‖A‖₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ :=
  Subtype.ext <| linfty_opNorm_def A
@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_def := linfty_opNNNorm_def
@[simp]
theorem linfty_opNNNorm_col (v : m → α) : ‖col ι v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  simp
@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_col := linfty_opNNNorm_col
@[simp]
theorem linfty_opNorm_col (v : m → α) : ‖col ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_col v
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_col := linfty_opNorm_col
@[simp]
theorem linfty_opNNNorm_row (v : n → α) : ‖row ι v‖₊ = ∑ i, ‖v i‖₊ := by
  simp [linfty_opNNNorm_def]
@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_row := linfty_opNNNorm_row
@[simp]
theorem linfty_opNorm_row (v : n → α) : ‖row ι v‖ = ∑ i, ‖v i‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_row v).trans <| by simp [NNReal.coe_sum]
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_row := linfty_opNorm_row
@[simp]
theorem linfty_opNNNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ i) fun j _hj hij => ?_).trans ?_
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
  · rw [diagonal_apply_eq]
@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_diagonal := linfty_opNNNorm_diagonal
@[simp]
theorem linfty_opNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_diagonal v
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_diagonal := linfty_opNorm_diagonal
end SeminormedAddCommGroup
section NonUnitalSeminormedRing
variable [NonUnitalSeminormedRing α]
theorem linfty_opNNNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ := by
  simp_rw [linfty_opNNNorm_def, Matrix.mul_apply]
  calc
    (Finset.univ.sup fun i => ∑ k, ‖∑ j, A i j * B j k‖₊) ≤
        Finset.univ.sup fun i => ∑ k, ∑ j, ‖A i j‖₊ * ‖B j k‖₊ :=
      Finset.sup_mono_fun fun i _hi =>
        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => nnnorm_mul_le _ _
    _ = Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * ∑ k, ‖B j k‖₊ := by
      simp_rw [@Finset.sum_comm m, Finset.mul_sum]
    _ ≤ Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      refine Finset.sup_mono_fun fun i _hi => ?_
      gcongr with j hj
      exact Finset.le_sup (f := fun i ↦ ∑ k : n, ‖B i k‖₊) hj
    _ ≤ (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      simp_rw [← Finset.sum_mul, ← NNReal.finset_sup_mul]
      rfl
@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_mul := linfty_opNNNorm_mul
theorem linfty_opNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNNNorm_mul _ _
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_mul := linfty_opNorm_mul
theorem linfty_opNNNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖₊ ≤ ‖A‖₊ * ‖v‖₊ := by
  rw [← linfty_opNNNorm_col (ι := Fin 1) (A *ᵥ v), ← linfty_opNNNorm_col v (ι := Fin 1)]
  exact linfty_opNNNorm_mul A (col (Fin 1) v)
@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_mulVec := linfty_opNNNorm_mulVec
theorem linfty_opNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖ :=
  linfty_opNNNorm_mulVec _ _
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_mulVec := linfty_opNorm_mulVec
end NonUnitalSeminormedRing
@[local instance]
protected def linftyOpNonUnitalSemiNormedRing [NonUnitalSeminormedRing α] :
    NonUnitalSeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpSeminormedAddCommGroup, Matrix.instNonUnitalRing with
    norm_mul := linfty_opNorm_mul }
instance linfty_opNormOneClass [SeminormedRing α] [NormOneClass α] [DecidableEq n] [Nonempty n] :
    NormOneClass (Matrix n n α) where norm_one := (linfty_opNorm_diagonal _).trans norm_one
@[local instance]
protected def linftyOpSemiNormedRing [SeminormedRing α] [DecidableEq n] :
    SeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }
@[local instance]
protected def linftyOpNonUnitalNormedRing [NonUnitalNormedRing α] :
    NonUnitalNormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
@[local instance]
protected def linftyOpNormedRing [NormedRing α] [DecidableEq n] : NormedRing (Matrix n n α) :=
  { Matrix.linftyOpSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
@[local instance]
protected def linftyOpNormedAlgebra [NormedField R] [SeminormedRing α] [NormedAlgebra R α]
    [DecidableEq n] : NormedAlgebra R (Matrix n n α) :=
  { Matrix.linftyOpNormedSpace, Matrix.instAlgebra with }
section
variable [NormedDivisionRing α] [NormedAlgebra ℝ α]
private def unitOf (a : α) : α := by classical exact if a = 0 then 1 else ‖a‖ • a⁻¹
private theorem norm_unitOf (a : α) : ‖unitOf a‖₊ = 1 := by
  rw [unitOf]
  split_ifs with h
  · simp
  · rw [← nnnorm_eq_zero] at h
    rw [nnnorm_smul, nnnorm_inv, nnnorm_norm, mul_inv_cancel₀ h]
private theorem mul_unitOf (a : α) : a * unitOf a = algebraMap _ _ (‖a‖₊ : ℝ)  := by
  simp only [unitOf, coe_nnnorm]
  split_ifs with h
  · simp [h]
  · rw [mul_smul_comm, mul_inv_cancel₀ h, Algebra.algebraMap_eq_smul_one]
end
section
variable [NontriviallyNormedField α] [NormedAlgebra ℝ α]
lemma linfty_opNNNorm_eq_opNNNorm (A : Matrix m n α) :
    ‖A‖₊ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖₊ := by
  rw [ContinuousLinearMap.opNNNorm_eq_of_bounds _ (linfty_opNNNorm_mulVec _) fun N hN => ?_]
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  cases isEmpty_or_nonempty n
  · simp
  classical
  let x : n → α := fun j => unitOf (A i j)
  have hxn : ‖x‖₊ = 1 := by
    simp_rw [x, Pi.nnnorm_def, norm_unitOf, Finset.sup_const Finset.univ_nonempty]
  specialize hN x
  rw [hxn, mul_one, Pi.nnnorm_def, Finset.sup_le_iff] at hN
  replace hN := hN i (Finset.mem_univ _)
  dsimp [mulVec, dotProduct] at hN
  simp_rw [x, mul_unitOf, ← map_sum, nnnorm_algebraMap, ← NNReal.coe_sum, NNReal.nnnorm_eq,
    nnnorm_one, mul_one] at hN
  exact hN
@[deprecated (since := "2024-02-02")]
alias linfty_op_nnnorm_eq_op_nnnorm := linfty_opNNNorm_eq_opNNNorm
lemma linfty_opNorm_eq_opNorm (A : Matrix m n α) :
    ‖A‖ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_eq_opNNNorm A)
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_eq_op_norm := linfty_opNorm_eq_opNorm
variable [DecidableEq n]
@[simp] lemma linfty_opNNNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖₊ = ‖f‖₊ := by
  rw [linfty_opNNNorm_eq_opNNNorm]
  simp only [← toLin'_apply', toLin'_toMatrix']
@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_toMatrix := linfty_opNNNorm_toMatrix
@[simp] lemma linfty_opNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖ = ‖f‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_toMatrix f)
@[deprecated (since := "2024-02-02")] alias linfty_op_norm_toMatrix := linfty_opNorm_toMatrix
end
end LinftyOp
section frobenius
open scoped Matrix
@[local instance]
def frobeniusSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  inferInstanceAs (SeminormedAddCommGroup (PiLp 2 fun _i : m => PiLp 2 fun _j : n => α))
@[local instance]
def frobeniusNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : NormedAddCommGroup (PiLp 2 fun i : m => PiLp 2 fun j : n => α))
@[local instance]
theorem frobeniusBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [BoundedSMul R α] :
    BoundedSMul R (Matrix m n α) :=
  (by infer_instance : BoundedSMul R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))
@[local instance]
def frobeniusNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  (by infer_instance : NormedSpace R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))
section SeminormedAddCommGroup
variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
theorem frobenius_nnnorm_def (A : Matrix m n α) :
    ‖A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  change ‖(WithLp.equiv 2 _).symm fun i => (WithLp.equiv 2 _).symm fun j => A i j‖₊ = _
  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two,
    WithLp.equiv_symm_pi_apply]
theorem frobenius_norm_def (A : Matrix m n α) :
    ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) (frobenius_nnnorm_def A)).trans <| by simp [NNReal.coe_sum]
@[simp]
theorem frobenius_nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]
@[simp]
theorem frobenius_norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) :
    ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_map_eq A f fun a => Subtype.ext <| hf a : _)
@[simp]
theorem frobenius_nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ := by
  rw [frobenius_nnnorm_def, frobenius_nnnorm_def, Finset.sum_comm]
  simp_rw [Matrix.transpose_apply]  
@[simp]
theorem frobenius_norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_transpose A
@[simp]
theorem frobenius_nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose
@[simp]
theorem frobenius_norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_conjTranspose A
instance frobenius_normedStarGroup [StarAddMonoid α] [NormedStarGroup α] :
    NormedStarGroup (Matrix m m α) :=
  ⟨frobenius_norm_conjTranspose⟩
@[simp]
theorem frobenius_norm_row (v : m → α) : ‖row ι v‖ = ‖(WithLp.equiv 2 _).symm v‖ := by
  rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [row_apply, Real.rpow_two, WithLp.equiv_symm_pi_apply]
@[simp]
theorem frobenius_nnnorm_row (v : m → α) : ‖row ι v‖₊ = ‖(WithLp.equiv 2 _).symm v‖₊ :=
  Subtype.ext <| frobenius_norm_row v
@[simp]
theorem frobenius_norm_col (v : n → α) : ‖col ι v‖ = ‖(WithLp.equiv 2 _).symm v‖ := by
  simp_rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [col_apply, Real.rpow_two, WithLp.equiv_symm_pi_apply]
@[simp]
theorem frobenius_nnnorm_col (v : n → α) : ‖col ι v‖₊ = ‖(WithLp.equiv 2 _).symm v‖₊ :=
  Subtype.ext <| frobenius_norm_col v
@[simp]
theorem frobenius_nnnorm_diagonal [DecidableEq n] (v : n → α) :
    ‖diagonal v‖₊ = ‖(WithLp.equiv 2 _).symm v‖₊ := by
  simp_rw [frobenius_nnnorm_def, ← Finset.sum_product', Finset.univ_product_univ,
    PiLp.nnnorm_eq_of_L2]
  let s := (Finset.univ : Finset n).map ⟨fun i : n => (i, i), fun i j h => congr_arg Prod.fst h⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _hi his => ?_]
  · rw [Finset.sum_map, NNReal.sqrt_eq_rpow]
    dsimp
    simp_rw [diagonal_apply_eq, NNReal.rpow_two]
  · suffices i.1 ≠ i.2 by rw [diagonal_apply_ne _ this, nnnorm_zero, NNReal.zero_rpow two_ne_zero]
    intro h
    exact Finset.mem_map.not.mp his ⟨i.1, Finset.mem_univ _, Prod.ext rfl h⟩
@[simp]
theorem frobenius_norm_diagonal [DecidableEq n] (v : n → α) :
    ‖diagonal v‖ = ‖(WithLp.equiv 2 _).symm v‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_diagonal v : _).trans rfl
end SeminormedAddCommGroup
theorem frobenius_nnnorm_one [DecidableEq n] [SeminormedAddCommGroup α] [One α] :
    ‖(1 : Matrix n n α)‖₊ = NNReal.sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
  refine (frobenius_nnnorm_diagonal _).trans ?_
  erw [PiLp.nnnorm_equiv_symm_const ENNReal.two_ne_top]
  simp_rw [NNReal.sqrt_eq_rpow]
  simp only [ENNReal.toReal_div, ENNReal.one_toReal, ENNReal.toReal_ofNat]
section RCLike
variable [RCLike α]
theorem frobenius_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ := by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← NNReal.mul_rpow, @Finset.sum_comm _ _ m, Finset.sum_mul_sum]
  gcongr with i _ j
  rw [← NNReal.rpow_le_rpow_iff one_half_pos, ← NNReal.rpow_mul,
    mul_div_cancel₀ (1 : ℝ) two_ne_zero, NNReal.rpow_one, NNReal.mul_rpow]
  have :=
    @nnnorm_inner_le_nnnorm α _ _ _ _ ((WithLp.equiv 2 <| _ → α).symm fun j => star (A i j))
      ((WithLp.equiv 2 <| _ → α).symm fun k => B k j)
  simpa only [WithLp.equiv_symm_pi_apply, PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    Pi.nnnorm_def, PiLp.nnnorm_eq_of_L2, star_star, nnnorm_star, NNReal.sqrt_eq_rpow,
    NNReal.rpow_two] using this
theorem frobenius_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  frobenius_nnnorm_mul A B
@[local instance]
def frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α) :=
  { Matrix.frobeniusSeminormedAddCommGroup, Matrix.instRing with
    norm := Norm.norm
    norm_mul := frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
@[local instance]
def frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α] :
    NormedAlgebra R (Matrix m m α) :=
  { Matrix.frobeniusNormedSpace, Matrix.instAlgebra with }
end RCLike
end frobenius
end Matrix