import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Analysis.Normed.Lp.ProdLp
variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A]
namespace WithLp
open Unitization
noncomputable def unitization_addEquiv_prod : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A) :=
  (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toAddEquiv.trans <|
    (addEquiv 𝕜 A).trans (WithLp.linearEquiv 1 𝕜 (𝕜 × A)).symm.toAddEquiv
noncomputable instance instUnitizationNormedAddCommGroup :
    NormedAddCommGroup (WithLp 1 (Unitization 𝕜 A)) :=
  NormedAddCommGroup.induced (WithLp 1 (Unitization 𝕜 A)) (WithLp 1 (𝕜 × A))
    (unitization_addEquiv_prod 𝕜 A) (AddEquiv.injective _)
noncomputable def uniformEquiv_unitization_addEquiv_prod :
    WithLp 1 (Unitization 𝕜 A) ≃ᵤ WithLp 1 (𝕜 × A) :=
  { unitization_addEquiv_prod 𝕜 A with
    uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id
    uniformContinuous_toFun := uniformContinuous_iff.mpr le_rfl }
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (WithLp 1 (Unitization 𝕜 A)) :=
  completeSpace_congr (uniformEquiv_unitization_addEquiv_prod 𝕜 A).isUniformEmbedding |>.mpr
    CompleteSpace.prod
variable {𝕜 A}
open ENNReal in
lemma unitization_norm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖ = ‖(WithLp.equiv 1 _ x).fst‖ + ‖(WithLp.equiv 1 _ x).snd‖ := calc
  ‖x‖ = (‖(WithLp.equiv 1 _ x).fst‖ ^ (1 : ℝ≥0∞).toReal +
      ‖(WithLp.equiv 1 _ x).snd‖ ^ (1 : ℝ≥0∞).toReal) ^ (1 / (1 : ℝ≥0∞).toReal) :=
    WithLp.prod_norm_eq_add (by simp : 0 < (1 : ℝ≥0∞).toReal) _
  _   = ‖(WithLp.equiv 1 _ x).fst‖ + ‖(WithLp.equiv 1 _ x).snd‖ := by simp
lemma unitization_nnnorm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖₊ = ‖(WithLp.equiv 1 _ x).fst‖₊ + ‖(WithLp.equiv 1 _ x).snd‖₊ :=
  Subtype.ext <| unitization_norm_def x
lemma unitization_norm_inr (x : A) : ‖(WithLp.equiv 1 (Unitization 𝕜 A)).symm x‖ = ‖x‖ := by
  simp [unitization_norm_def]
lemma unitization_nnnorm_inr (x : A) : ‖(WithLp.equiv 1 (Unitization 𝕜 A)).symm x‖₊ = ‖x‖₊ := by
  simp [unitization_nnnorm_def]
lemma unitization_isometry_inr :
    Isometry (fun x : A ↦ (WithLp.equiv 1 (Unitization 𝕜 A)).symm x) :=
  AddMonoidHomClass.isometry_of_norm
    ((WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.comp <| Unitization.inrHom 𝕜 A)
    unitization_norm_inr
variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
instance instUnitizationRing : Ring (WithLp 1 (Unitization 𝕜 A)) :=
  inferInstanceAs (Ring (Unitization 𝕜 A))
@[simp]
lemma unitization_mul (x y : WithLp 1 (Unitization 𝕜 A)) :
    WithLp.equiv 1 _ (x * y) = (WithLp.equiv 1 _ x) * (WithLp.equiv 1 _ y) :=
  rfl
instance {R : Type*} [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A] [IsScalarTower R 𝕜 A] :
    Algebra R (WithLp 1 (Unitization 𝕜 A)) :=
  inferInstanceAs (Algebra R (Unitization 𝕜 A))
@[simp]
lemma unitization_algebraMap (r : 𝕜) :
    WithLp.equiv 1 _ (algebraMap 𝕜 (WithLp 1 (Unitization 𝕜 A)) r) =
      algebraMap 𝕜 (Unitization 𝕜 A) r :=
  rfl
@[simps!]
def unitizationAlgEquiv (R : Type*) [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A]
    [IsScalarTower R 𝕜 A] : WithLp 1 (Unitization 𝕜 A) ≃ₐ[R] Unitization 𝕜 A :=
  { WithLp.equiv 1 (Unitization 𝕜 A) with
    map_mul' := fun _ _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }
noncomputable instance instUnitizationNormedRing : NormedRing (WithLp 1 (Unitization 𝕜 A)) where
  dist_eq := dist_eq_norm
  norm_mul x y := by
    simp_rw [unitization_norm_def, add_mul, mul_add, unitization_mul, fst_mul, snd_mul]
    rw [add_assoc, add_assoc]
    gcongr
    · exact norm_mul_le _ _
    · apply (norm_add_le _ _).trans
      gcongr
      · simp [norm_smul]
      · apply (norm_add_le _ _).trans
        gcongr
        · simp [norm_smul, mul_comm]
        · exact norm_mul_le _ _
noncomputable instance instUnitizationNormedAlgebra :
    NormedAlgebra 𝕜 (WithLp 1 (Unitization 𝕜 A)) where
  norm_smul_le r x := by
    simp_rw [unitization_norm_def, equiv_smul, fst_smul, snd_smul, norm_smul, mul_add]
    exact le_rfl
end WithLp