import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.UniformSpace.Matrix
open scoped Matrix
open NormedSpace 
variable (𝕂 : Type*) {m n : Type*} {n' : m → Type*} {𝔸 : Type*}
namespace Matrix
section Topological
section Ring
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [Field 𝕂] [Ring 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]
  [Algebra 𝕂 𝔸] [T2Space 𝔸]
theorem exp_diagonal (v : m → 𝔸) : exp 𝕂 (diagonal v) = diagonal (exp 𝕂 v) := by
  simp_rw [exp_eq_tsum, diagonal_pow, ← diagonal_smul, ← diagonal_tsum]
theorem exp_blockDiagonal (v : m → Matrix n n 𝔸) :
    exp 𝕂 (blockDiagonal v) = blockDiagonal (exp 𝕂 v) := by
  simp_rw [exp_eq_tsum, ← blockDiagonal_pow, ← blockDiagonal_smul, ← blockDiagonal_tsum]
theorem exp_blockDiagonal' (v : ∀ i, Matrix (n' i) (n' i) 𝔸) :
    exp 𝕂 (blockDiagonal' v) = blockDiagonal' (exp 𝕂 v) := by
  simp_rw [exp_eq_tsum, ← blockDiagonal'_pow, ← blockDiagonal'_smul, ← blockDiagonal'_tsum]
theorem exp_conjTranspose [StarRing 𝔸] [ContinuousStar 𝔸] (A : Matrix m m 𝔸) :
    exp 𝕂 Aᴴ = (exp 𝕂 A)ᴴ :=
  (star_exp A).symm
theorem IsHermitian.exp [StarRing 𝔸] [ContinuousStar 𝔸] {A : Matrix m m 𝔸} (h : A.IsHermitian) :
    (exp 𝕂 A).IsHermitian :=
  (exp_conjTranspose _ _).symm.trans <| congr_arg _ h
end Ring
section CommRing
variable [Fintype m] [DecidableEq m] [Field 𝕂] [CommRing 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸]
  [Algebra 𝕂 𝔸] [T2Space 𝔸]
theorem exp_transpose (A : Matrix m m 𝔸) : exp 𝕂 Aᵀ = (exp 𝕂 A)ᵀ := by
  simp_rw [exp_eq_tsum, transpose_tsum, transpose_smul, transpose_pow]
theorem IsSymm.exp {A : Matrix m m 𝔸} (h : A.IsSymm) : (exp 𝕂 A).IsSymm :=
  (exp_transpose _ _).symm.trans <| congr_arg _ h
end CommRing
end Topological
section Normed
variable [RCLike 𝕂] [Fintype m] [DecidableEq m]
  [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
nonrec theorem exp_add_of_commute (A B : Matrix m m 𝔸) (h : Commute A B) :
    exp 𝕂 (A + B) = exp 𝕂 A * exp 𝕂 B := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_add_of_commute h
nonrec theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → Matrix m m 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp 𝕂 (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp 𝕂 (f i)) fun _ hi _ hj _ => (h.of_refl hi hj).exp 𝕂 := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_sum_of_commute s f h
nonrec theorem exp_nsmul (n : ℕ) (A : Matrix m m 𝔸) : exp 𝕂 (n • A) = exp 𝕂 A ^ n := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_nsmul n A
nonrec theorem isUnit_exp (A : Matrix m m 𝔸) : IsUnit (exp 𝕂 A) := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact isUnit_exp _ A
nonrec theorem exp_units_conj (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp 𝕂 (U * A * U⁻¹) = U * exp 𝕂 A * U⁻¹ := by
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact exp_units_conj _ U A
theorem exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp 𝕂 (U⁻¹ * A * U) = U⁻¹ * exp 𝕂 A * U :=
  exp_units_conj 𝕂 U⁻¹ A
end Normed
section NormedComm
variable [RCLike 𝕂] [Fintype m] [DecidableEq m]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
theorem exp_neg (A : Matrix m m 𝔸) : exp 𝕂 (-A) = (exp 𝕂 A)⁻¹ := by
  rw [nonsing_inv_eq_ring_inverse]
  letI : SeminormedRing (Matrix m m 𝔸) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix m m 𝔸) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra 𝕂 (Matrix m m 𝔸) := Matrix.linftyOpNormedAlgebra
  exact (Ring.inverse_exp _ A).symm
theorem exp_zsmul (z : ℤ) (A : Matrix m m 𝔸) : exp 𝕂 (z • A) = exp 𝕂 A ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · have : IsUnit (exp 𝕂 A).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_exp _ _)
    rw [Matrix.zpow_neg this, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]
theorem exp_conj (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp 𝕂 (U * A * U⁻¹) = U * exp 𝕂 A * U⁻¹ :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj 𝕂 u A
theorem exp_conj' (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp 𝕂 (U⁻¹ * A * U) = U⁻¹ * exp 𝕂 A * U :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj' 𝕂 u A
end NormedComm
end Matrix