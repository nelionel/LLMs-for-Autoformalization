import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul
suppress_compilation
variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
open ContinuousLinearMap
namespace Unitization
def splitMul : Unitization 𝕜 A →ₐ[𝕜] 𝕜 × (A →L[𝕜] A) :=
  (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)
variable {𝕜 A}
@[simp]
theorem splitMul_apply (x : Unitization 𝕜 A) :
    splitMul 𝕜 A x = (x.fst, algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd) :=
  show (x.fst + 0, _) = (x.fst, _) by rw [add_zero]; rfl
theorem splitMul_injective_of_clm_mul_injective
    (h : Function.Injective (mul 𝕜 A)) :
    Function.Injective (splitMul 𝕜 A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x
  rw [map_add] at hx
  simp only [splitMul_apply, fst_inl, snd_inl, map_zero, add_zero, fst_inr, snd_inr,
    zero_add, Prod.mk_add_mk, Prod.mk_eq_zero] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [map_zero, zero_add, inl_zero] at hx ⊢
  rw [← map_zero (mul 𝕜 A)] at hx
  rw [h hx, inr_zero]
variable [RegularNormedAlgebra 𝕜 A]
variable (𝕜 A)
theorem splitMul_injective : Function.Injective (splitMul 𝕜 A) :=
  splitMul_injective_of_clm_mul_injective (isometry_mul 𝕜 A).injective
variable {𝕜 A}
section Aux
noncomputable abbrev normedRingAux : NormedRing (Unitization 𝕜 A) :=
  NormedRing.induced (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (splitMul 𝕜 A) (splitMul_injective 𝕜 A)
attribute [local instance] Unitization.normedRingAux
noncomputable abbrev normedAlgebraAux : NormedAlgebra 𝕜 (Unitization 𝕜 A) :=
  NormedAlgebra.induced 𝕜 (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (splitMul 𝕜 A)
attribute [local instance] Unitization.normedAlgebraAux
theorem norm_def (x : Unitization 𝕜 A) : ‖x‖ = ‖splitMul 𝕜 A x‖ :=
  rfl
theorem nnnorm_def (x : Unitization 𝕜 A) : ‖x‖₊ = ‖splitMul 𝕜 A x‖₊ :=
  rfl
theorem norm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖ = ‖x.fst‖ ⊔ ‖algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖ := by
  rw [norm_def, splitMul_apply, Prod.norm_def]
theorem nnnorm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖₊ = ‖x.fst‖₊ ⊔ ‖algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖₊ :=
  NNReal.eq <| norm_eq_sup x
theorem lipschitzWith_addEquiv :
    LipschitzWith 2 (Unitization.addEquiv 𝕜 A) := by
  rw [← Real.toNNReal_ofNat]
  refine AddMonoidHomClass.lipschitz_of_bound (Unitization.addEquiv 𝕜 A) 2 fun x => ?_
  rw [norm_eq_sup, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    rw [two_mul]
    calc
      ‖x.snd‖ = ‖mul 𝕜 A x.snd‖ :=
        .symm <| (isometry_mul 𝕜 A).norm_map_of_map_zero (map_zero _) _
      _ ≤ ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ + ‖x.fst‖ := by
        simpa only [add_comm _ (mul 𝕜 A x.snd), norm_algebraMap'] using
          norm_le_add_norm_add (mul 𝕜 A x.snd) (algebraMap 𝕜 _ x.fst)
      _ ≤ _ := add_le_add le_sup_right le_sup_left
theorem antilipschitzWith_addEquiv :
    AntilipschitzWith 2 (addEquiv 𝕜 A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound (addEquiv 𝕜 A) fun x => ?_
  rw [norm_eq_sup, Prod.norm_def, NNReal.coe_two]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    calc
      ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ ≤ ‖algebraMap 𝕜 _ x.fst‖ + ‖mul 𝕜 A x.snd‖ :=
        norm_add_le _ _
      _ = ‖x.fst‖ + ‖x.snd‖ := by
        rw [norm_algebraMap', (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 A)).mp (isometry_mul 𝕜 A)]
      _ ≤ _ := (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm
open Bornology Filter
open scoped Uniformity Topology
theorem uniformity_eq_aux :
    𝓤[instUniformSpaceProd.comap <| addEquiv 𝕜 A] = 𝓤 (Unitization 𝕜 A) := by
  have key : IsUniformInducing (addEquiv 𝕜 A) :=
    antilipschitzWith_addEquiv.isUniformInducing lipschitzWith_addEquiv.uniformContinuous
  rw [← key.comap_uniformity]
  rfl
theorem cobounded_eq_aux :
    @cobounded _ (Bornology.induced <| addEquiv 𝕜 A) = cobounded (Unitization 𝕜 A) :=
  le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
    antilipschitzWith_addEquiv.tendsto_cobounded.le_comap
end Aux
instance instUniformSpace : UniformSpace (Unitization 𝕜 A) :=
  instUniformSpaceProd.comap (addEquiv 𝕜 A)
def uniformEquivProd : (Unitization 𝕜 A) ≃ᵤ (𝕜 × A) :=
  Equiv.toUniformEquivOfIsUniformInducing (addEquiv 𝕜 A) ⟨rfl⟩
instance instBornology : Bornology (Unitization 𝕜 A) :=
  Bornology.induced <| addEquiv 𝕜 A
theorem isUniformEmbedding_addEquiv {𝕜} [NontriviallyNormedField 𝕜] :
    IsUniformEmbedding (addEquiv 𝕜 A) where
  comap_uniformity := rfl
  injective := (addEquiv 𝕜 A).injective
@[deprecated (since := "2024-10-01")]
alias uniformEmbedding_addEquiv := isUniformEmbedding_addEquiv
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (Unitization 𝕜 A) :=
  uniformEquivProd.completeSpace_iff.2 .prod
noncomputable instance instMetricSpace : MetricSpace (Unitization 𝕜 A) :=
  (normedRingAux.toMetricSpace.replaceUniformity uniformity_eq_aux).replaceBornology
    fun s => Filter.ext_iff.1 cobounded_eq_aux (sᶜ)
noncomputable instance instNormedRing : NormedRing (Unitization 𝕜 A) where
  dist_eq := normedRingAux.dist_eq
  norm_mul := normedRingAux.norm_mul
  norm := normedRingAux.norm
instance instNormedAlgebra : NormedAlgebra 𝕜 (Unitization 𝕜 A) where
  norm_smul_le k x := by
    rw [norm_def, map_smul]
    exact (norm_smul k (splitMul 𝕜 A x)).le
instance instNormOneClass : NormOneClass (Unitization 𝕜 A) where
  norm_one := by simpa only [norm_eq_sup, fst_one, norm_one, snd_one, map_one, map_zero,
      add_zero, sup_eq_left] using opNorm_le_bound _ zero_le_one fun x => by simp
lemma norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖ := by
  simp [norm_eq_sup]
lemma nnnorm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inr a
lemma isometry_inr : Isometry ((↑) : A → Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm (inrNonUnitalAlgHom 𝕜 A) norm_inr
@[fun_prop]
theorem continuous_inr : Continuous (inr : A → Unitization 𝕜 A) :=
  isometry_inr.continuous
lemma dist_inr (a b : A) : dist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = dist a b :=
  isometry_inr.dist_eq a b
lemma nndist_inr (a b : A) : nndist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = nndist a b :=
  isometry_inr.nndist_eq a b
example : (instNormedRing (𝕜 := 𝕜) (A := A)).toMetricSpace = instMetricSpace := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toBornology = instBornology := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toUniformSpace = instUniformSpace := rfl
end Unitization