import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
universe u v w z
open scoped Matrix
open Matrix Module Fintype Polynomial Finset IntermediateField
namespace Algebra
variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w} [DecidableEq ι]
variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
section Discr
noncomputable def discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι → B) := (traceMatrix A b).det
theorem discr_def [Fintype ι] (b : ι → B) : discr A b = (traceMatrix A b).det := rfl
variable {A C} in
theorem discr_eq_discr_of_algEquiv [Fintype ι] (b : ι → B) (f : B ≃ₐ[A] C) :
    Algebra.discr A b = Algebra.discr A (f ∘ b) := by
  rw [discr_def]; congr; ext
  simp_rw [traceMatrix_apply, traceForm_apply, Function.comp, ← map_mul f, trace_eq_of_algEquiv]
variable {ι' : Type*} [Fintype ι'] [Fintype ι] [DecidableEq ι']
section Basic
@[simp]
theorem discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : discr A (b ∘ ⇑f.symm) = discr A b := by
  classical rw [← Basis.coe_reindex, discr_def, traceMatrix_reindex, det_reindex_self, ← discr_def]
theorem discr_zero_of_not_linearIndependent [IsDomain A] {b : ι → B}
    (hli : ¬LinearIndependent A b) : discr A b = 0 := by
  classical
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have : (traceMatrix A b) *ᵥ g = 0 := by
    ext i
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by
      intro j
      simp [mul_comm]
    simp only [mulVec, dotProduct, traceMatrix_apply, Pi.zero_apply, traceForm_apply, fun j =>
      this j, ← map_sum, ← sum_mul, hg, zero_mul, LinearMap.map_zero]
  by_contra h
  rw [discr_def] at h
  simp [Matrix.eq_zero_of_mulVec_eq_zero h this] at hi
variable {A}
theorem discr_of_matrix_vecMul (b : ι → B) (P : Matrix ι ι A) :
    discr A (b ᵥ* P.map (algebraMap A B)) = P.det ^ 2 * discr A b := by
  rw [discr_def, traceMatrix_of_matrix_vecMul, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
theorem discr_of_matrix_mulVec (b : ι → B) (P : Matrix ι ι A) :
    discr A (P.map (algebraMap A B) *ᵥ b) = P.det ^ 2 * discr A b := by
  rw [discr_def, traceMatrix_of_matrix_mulVec, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
end Basic
section Field
variable (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]
variable [Algebra K L] [Algebra K E]
variable [Module.Finite K L] [IsAlgClosed E]
theorem discr_not_zero_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) :
    discr K b ≠ 0 := by
  rw [discr_def, traceMatrix_of_basis, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  exact traceForm_nondegenerate _ _
theorem discr_isUnit_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) : IsUnit (discr K b) :=
  IsUnit.mk0 _ (discr_not_zero_of_basis _ _)
variable (b : ι → L) (pb : PowerBasis K L)
theorem discr_eq_det_embeddingsMatrixReindex_pow_two
    [Algebra.IsSeparable K L] (e : ι ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K b) = (embeddingsMatrixReindex K E b e).det ^ 2 := by
  rw [discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    traceMatrix_eq_embeddingsMatrixReindex_mul_trans, det_mul, det_transpose, pow_two]
theorem discr_powerBasis_eq_prod (e : Fin pb.dim ≃ (L →ₐ[K] E)) [Algebra.IsSeparable K L] :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
  rw [discr_eq_det_embeddingsMatrixReindex_pow_two K E pb.basis e,
    embeddingsMatrixReindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow]
  congr; ext i
  rw [← prod_pow]
theorem discr_powerBasis_eq_prod' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Ioi i, -((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)) := by
  rw [discr_powerBasis_eq_prod _ _ _ e]
  congr; ext i; congr; ext j
  ring
local notation "n" => finrank K L
theorem discr_powerBasis_eq_prod'' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      (-1) ^ (n * (n - 1) / 2) *
        ∏ i : Fin pb.dim, ∏ j ∈ Ioi i, (e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen) := by
  rw [discr_powerBasis_eq_prod' _ _ _ e]
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)),
    prod_mul_distrib]
  congr
  simp only [prod_pow_eq_pow_sum, prod_const]
  congr
  rw [← @Nat.cast_inj ℚ, Nat.cast_sum]
  have : ∀ x : Fin pb.dim, ↑x + 1 ≤ pb.dim := by simp [Nat.succ_le_iff, Fin.is_lt]
  simp_rw [Fin.card_Ioi, Nat.sub_sub, add_comm 1]
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    Nat.cast_add, Nat.cast_one, sum_add_distrib, mul_one]
  rw [← Nat.cast_sum, ← @Finset.sum_range ℕ _ pb.dim fun i => i, sum_range_id]
  have hn : n = pb.dim := by
    rw [← AlgHom.card K L E, ← Fintype.card_fin pb.dim]
    exact Fintype.card_congr e.symm
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := pb.dim.even_mul_pred_self.two_dvd
  have hne : ((2 : ℕ) : ℚ) ≠ 0 := by simp
  have hle : 1 ≤ pb.dim := by
    rw [← hn, Nat.one_le_iff_ne_zero, ← zero_lt_iff, Module.finrank_pos_iff]
    infer_instance
  rw [hn, Nat.cast_div h₂ hne, Nat.cast_mul, Nat.cast_sub hle]
  field_simp
  ring
theorem discr_powerBasis_eq_norm [Algebra.IsSeparable K L] :
    discr K pb.basis =
      (-1) ^ (n * (n - 1) / 2) *
      norm K (aeval pb.gen (derivative (R := K) (minpoly K pb.gen))) := by
  let E := AlgebraicClosure L
  letI := fun a b : E => Classical.propDecidable (Eq a b)
  have e : Fin pb.dim ≃ (L →ₐ[K] E) := by
    refine equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : ((minpoly K pb.gen).aroots E).Nodup :=
    nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ (minpoly K pb.gen).aroots E := by
    intro σ
    rw [mem_roots, IsRoot.def, eval_map, ← aeval_def, aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero (Algebra.IsSeparable.isIntegral K pb.gen)]
  apply (algebraMap K E).injective
  rw [RingHom.map_mul, RingHom.map_pow, RingHom.map_neg, RingHom.map_one,
    discr_powerBasis_eq_prod'' _ _ _ e]
  congr
  rw [norm_eq_prod_embeddings, prod_prod_Ioi_mul_eq_prod_prod_off_diag]
  conv_rhs =>
    congr
    rfl
    ext σ
    rw [← aeval_algHom_apply,
      aeval_root_derivative_of_splits (minpoly.monic (Algebra.IsSeparable.isIntegral K pb.gen))
        (IsAlgClosed.splits_codomain _) (hroots σ),
      ← Finset.prod_mk _ (hnodup.erase _)]
  rw [prod_sigma', prod_sigma']
  refine prod_bij' (fun i _ ↦ ⟨e i.2, e i.1 pb.gen⟩)
    (fun σ hσ ↦ ⟨e.symm (PowerBasis.lift pb σ.2 ?_), e.symm σ.1⟩) ?_ ?_ ?_ ?_ (fun i _ ↦ by simp)
    <;> simp only [mem_sigma, mem_univ, Finset.mem_mk, hnodup.mem_erase_iff, IsRoot.def,
      mem_roots', minpoly.ne_zero (Algebra.IsSeparable.isIntegral K pb.gen), not_false_eq_true,
      mem_singleton, true_and, @mem_compl _ _ _ (_), Sigma.forall, Equiv.apply_symm_apply,
      PowerBasis.lift_gen, and_imp, implies_true, forall_const, Equiv.symm_apply_apply,
      Sigma.ext_iff, Equiv.symm_apply_eq, heq_eq_eq, and_true] at *
  · simpa only [aeval_def, eval₂_eq_eval_map] using hσ.2.2
  · exact fun a b hba ↦ ⟨fun h ↦ hba <| e.injective <| pb.algHom_ext h.symm, hroots _⟩
  · rintro a b hba ha
    rw [ha, PowerBasis.lift_gen] at hba
    exact hba.1 rfl
  · exact fun a b _ ↦ pb.algHom_ext <| pb.lift_gen _ _
section Integral
variable {R : Type z} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
theorem discr_isIntegral {b : ι → L} (h : ∀ i, IsIntegral R (b i)) : IsIntegral R (discr K b) := by
  classical
  rw [discr_def]
  exact IsIntegral.det fun i j ↦ isIntegral_trace ((h i).mul (h j))
theorem discr_mul_isIntegral_mem_adjoin [Algebra.IsSeparable K L] [IsIntegrallyClosed R]
    [IsFractionRing R K] {B : PowerBasis K L} (hint : IsIntegral R B.gen) {z : L}
    (hz : IsIntegral R z) : discr K B.basis • z ∈ adjoin R ({B.gen} : Set L) := by
  have hinv : IsUnit (traceMatrix K B.basis).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ B.basis
  have H :
    (traceMatrix K B.basis).det • (traceMatrix K B.basis) *ᵥ (B.basis.equivFun z) =
      (traceMatrix K B.basis).det • fun i => trace K L (z * B.basis i) := by
    congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z * B.basis i)
  suffices ∀ i, ((traceMatrix K B.basis).det • B.basis.equivFun z) i ∈ (⊥ : Subalgebra R K) by
    rw [← B.basis.sum_repr z, Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    replace this := this i
    rw [← discr_def, Pi.smul_apply, mem_bot] at this
    obtain ⟨r, hr⟩ := this
    rw [Basis.equivFun_apply] at hr
    rw [← smul_assoc, ← hr, algebraMap_smul]
    refine Subalgebra.smul_mem _ ?_ _
    rw [B.basis_eq_pow i]
    exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
  intro i
  rw [← H, ← mulVec_smul] at cramer
  replace cramer := congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
  rw [mulVec_mulVec, nonsing_inv_mul _ hinv, mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec,
    one_mulVec] at cramer
  rw [← congr_fun cramer i, cramer_apply, det_apply]
  refine
    Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateColumn_apply, hji, eq_self_iff_true, PowerBasis.coe_basis]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul <| hint.pow _))
  · simp only [updateColumn_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2
      (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace <| (hint.pow _).mul (hint.pow _))
end Integral
end Field
section Int
theorem discr_eq_discr (b : Basis ι ℤ A) (b' : Basis ι ℤ A) :
    Algebra.discr ℤ b = Algebra.discr ℤ b' := by
  convert Algebra.discr_of_matrix_vecMul b' (b'.toMatrix b)
  · rw [Basis.toMatrix_map_vecMul]
  · suffices IsUnit (b'.toMatrix b).det by
      rw [Int.isUnit_iff, ← sq_eq_one_iff] at this
      rw [this, one_mul]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl ℤ A) b b'
end Int
end Discr
end Algebra