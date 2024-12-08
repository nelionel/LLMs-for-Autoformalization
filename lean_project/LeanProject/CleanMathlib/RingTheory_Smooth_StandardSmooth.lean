import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Presentation
universe t t' w w' u v
open TensorProduct MvPolynomial Classical
variable (n m : ℕ)
namespace Algebra
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
@[nolint checkUnivs]
structure PreSubmersivePresentation extends Algebra.Presentation.{t, w} R S where
  map : rels → vars
  map_inj : Function.Injective map
  relations_finite : Finite rels
namespace PreSubmersivePresentation
attribute [instance] relations_finite
variable {R S}
variable (P : PreSubmersivePresentation R S)
lemma card_relations_le_card_vars_of_isFinite [P.IsFinite] :
    Nat.card P.rels ≤ Nat.card P.vars :=
  Nat.card_le_card_of_injective P.map P.map_inj
noncomputable abbrev basis : Basis P.rels P.Ring (P.rels → P.Ring) :=
  Pi.basisFun P.Ring P.rels
noncomputable def differential : (P.rels → P.Ring) →ₗ[P.Ring] (P.rels → P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : P.rels ↦ MvPolynomial.pderiv (P.map i) (P.relation j))
noncomputable def jacobian : S :=
  algebraMap P.Ring S <| LinearMap.det P.differential
section Matrix
variable [Fintype P.rels] [DecidableEq P.rels]
noncomputable def jacobiMatrix : Matrix P.rels P.rels P.Ring :=
  LinearMap.toMatrix P.basis P.basis P.differential
lemma jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det := by
   simp [jacobiMatrix, jacobian]
lemma jacobiMatrix_apply (i j : P.rels) :
    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]
end Matrix
section Constructions
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    PreSubmersivePresentation.{t, w} R S where
  toPresentation := Presentation.ofBijectiveAlgebraMap.{t, w} h
  map := PEmpty.elim
  map_inj (a b : PEmpty) h := by contradiction
  relations_finite := inferInstanceAs (Finite PEmpty.{t + 1})
instance (h : Function.Bijective (algebraMap R S)) : Fintype (ofBijectiveAlgebraMap h).vars :=
  inferInstanceAs (Fintype PEmpty)
instance (h : Function.Bijective (algebraMap R S)) : Fintype (ofBijectiveAlgebraMap h).rels :=
  inferInstanceAs (Fintype PEmpty)
@[simp]
lemma ofBijectiveAlgebraMap_jacobian (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).jacobian = 1 := by
  have : (algebraMap (ofBijectiveAlgebraMap h).Ring S).mapMatrix
      (ofBijectiveAlgebraMap h).jacobiMatrix = 1 := by
    ext (i j : PEmpty)
    contradiction
  rw [jacobian_eq_jacobiMatrix_det, RingHom.map_det, this, Matrix.det_one]
section Localization
variable (r : R) [IsLocalization.Away r S]
variable (S) in
@[simps map]
noncomputable def localizationAway : PreSubmersivePresentation R S where
  __ := Presentation.localizationAway S r
  map _ := ()
  map_inj _ _ h := h
  relations_finite := inferInstanceAs <| Finite Unit
instance : Fintype (localizationAway S r).rels :=
  inferInstanceAs (Fintype Unit)
instance : DecidableEq (localizationAway S r).rels :=
  inferInstanceAs (DecidableEq Unit)
@[simp]
lemma localizationAway_jacobiMatrix :
    (localizationAway S r).jacobiMatrix = Matrix.diagonal (fun () ↦ MvPolynomial.C r) := by
  have h : (pderiv ()) (C r * X () - 1) = C r := by simp
  ext (i : Unit) (j : Unit) : 1
  rwa [jacobiMatrix_apply]
@[simp]
lemma localizationAway_jacobian : (localizationAway S r).jacobian = algebraMap R S r := by
  rw [jacobian_eq_jacobiMatrix_det, localizationAway_jacobiMatrix]
  simp [show Fintype.card (localizationAway r (S := S)).rels = 1 from rfl]
end Localization
section Composition
variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : PreSubmersivePresentation S T) (P : PreSubmersivePresentation R S)
@[simps map]
noncomputable def comp : PreSubmersivePresentation R T where
  __ := Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq ↦ Sum.inl <| Q.map rq) (fun rp ↦ Sum.inr <| P.map rp)
  map_inj := Function.Injective.sum_elim ((Sum.inl_injective).comp (Q.map_inj))
    ((Sum.inr_injective).comp (P.map_inj)) <| by simp
  relations_finite := inferInstanceAs <| Finite (Q.rels ⊕ P.rels)
lemma dimension_comp_eq_dimension_add_dimension [Q.IsFinite] [P.IsFinite] :
    (Q.comp P).dimension = Q.dimension + P.dimension := by
  simp only [Presentation.dimension]
  erw [Presentation.comp_rels, Generators.comp_vars]
  have : Nat.card P.rels ≤ Nat.card P.vars :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card Q.rels ≤ Nat.card Q.vars :=
    card_relations_le_card_vars_of_isFinite Q
  simp only [Nat.card_sum]
  omega
section
variable [Fintype (Q.comp P).rels]
private lemma jacobiMatrix_comp_inl_inr (i : Q.rels) (j : P.rels) :
    (Q.comp P).jacobiMatrix (Sum.inl i) (Sum.inr j) = 0 := by
  rw [jacobiMatrix_apply]
  refine MvPolynomial.pderiv_eq_zero_of_not_mem_vars (fun hmem ↦ ?_)
  apply MvPolynomial.vars_rename at hmem
  simp at hmem
private lemma jacobiMatrix_comp_₁₂ : (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0 := by
  ext i j : 1
  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]
section Q
variable [Fintype Q.rels]
private lemma jacobiMatrix_comp_inl_inl (i j : Q.rels) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val))
      ((Q.comp P).jacobiMatrix (Sum.inl j) (Sum.inl i)) = Q.jacobiMatrix j i := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply, comp_map, Sum.elim_inl,
    ← Q.comp_aeval_relation_inl P.toPresentation]
  apply aeval_sum_elim_pderiv_inl
private lemma jacobiMatrix_comp_₁₁_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det = Q.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det, AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P]
  apply aeval_sum_elim
end Q
section P
variable [Fintype P.rels]
private lemma jacobiMatrix_comp_inr_inr (i j : P.rels) :
    (Q.comp P).jacobiMatrix (Sum.inr i) (Sum.inr j) =
      MvPolynomial.rename Sum.inr (P.jacobiMatrix i j) := by
  rw [jacobiMatrix_apply, jacobiMatrix_apply]
  simp only [comp_map, Sum.elim_inr]
  apply pderiv_rename Sum.inr_injective
private lemma jacobiMatrix_comp_₂₂_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = algebraMap S T P.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det]
  rw [AlgHom.map_det (aeval (Q.comp P).val), RingHom.map_det, RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.toBlocks₂₂, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingHom.mapMatrix_apply, Generators.algebraMap_apply, map_aeval, coe_eval₂Hom]
  rw [jacobiMatrix_comp_inr_inr, ← IsScalarTower.algebraMap_eq]
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]
  generalize P.jacobiMatrix i j = p
  induction' p using MvPolynomial.induction_on with a p q hp hq p i hp
  · simp only [algHom_C, algebraMap_eq, eval₂_C]
    erw [MvPolynomial.eval₂_C]
  · simp [hp, hq]
  · simp only [map_mul, rename_X, eval₂_mul, hp, eval₂_X]
    erw [Generators.comp_val]
    simp
end P
end
@[simp]
lemma comp_jacobian_eq_jacobian_smul_jacobian : (Q.comp P).jacobian = P.jacobian • Q.jacobian := by
  cases nonempty_fintype Q.rels
  cases nonempty_fintype P.rels
  letI : Fintype (Q.comp P).rels := inferInstanceAs <| Fintype (Q.rels ⊕ P.rels)
  rw [jacobian_eq_jacobiMatrix_det, ← Matrix.fromBlocks_toBlocks ((Q.comp P).jacobiMatrix),
    jacobiMatrix_comp_₁₂]
  convert_to
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = P.jacobian • Q.jacobian
  · simp only [Generators.algebraMap_apply, ← map_mul]
    congr
    convert Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
      (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂
  · rw [jacobiMatrix_comp_₁₁_det, jacobiMatrix_comp_₂₂_det, mul_comm, Algebra.smul_def]
end Composition
section BaseChange
variable (T) [CommRing T] [Algebra R T] (P : PreSubmersivePresentation R S)
noncomputable def baseChange : PreSubmersivePresentation T (T ⊗[R] S) where
  __ := P.toPresentation.baseChange T
  map := P.map
  map_inj := P.map_inj
  relations_finite := P.relations_finite
@[simp]
lemma baseChange_jacobian : (P.baseChange T).jacobian = 1 ⊗ₜ P.jacobian := by
  classical
  cases nonempty_fintype P.rels
  letI : Fintype (P.baseChange T).rels := inferInstanceAs <| Fintype P.rels
  simp_rw [jacobian_eq_jacobiMatrix_det]
  have h : (baseChange T P).jacobiMatrix =
      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    erw [MvPolynomial.pderiv_map]
    rfl
  rw [h]
  erw [← RingHom.map_det, aeval_map_algebraMap]
  apply aeval_one_tmul
end BaseChange
end Constructions
end PreSubmersivePresentation
@[nolint checkUnivs]
structure SubmersivePresentation extends PreSubmersivePresentation.{t, w} R S where
  jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian
  isFinite : toPreSubmersivePresentation.IsFinite := by infer_instance
attribute [instance] SubmersivePresentation.isFinite
namespace SubmersivePresentation
open PreSubmersivePresentation
section Constructions
variable {R S} in
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    SubmersivePresentation.{t, w} R S where
  __ := PreSubmersivePresentation.ofBijectiveAlgebraMap.{t, w} h
  jacobian_isUnit := by
    rw [ofBijectiveAlgebraMap_jacobian]
    exact isUnit_one
  isFinite := Presentation.ofBijectiveAlgebraMap_isFinite h
noncomputable def id : SubmersivePresentation.{t, w} R R :=
  ofBijectiveAlgebraMap Function.bijective_id
section Composition
variable {R S T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : SubmersivePresentation S T) (P : SubmersivePresentation R S)
noncomputable def comp : SubmersivePresentation R T where
  __ := Q.toPreSubmersivePresentation.comp P.toPreSubmersivePresentation
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def, IsUnit.mul_iff]
    exact ⟨RingHom.isUnit_map _ <| P.jacobian_isUnit, Q.jacobian_isUnit⟩
  isFinite := Presentation.comp_isFinite Q.toPresentation P.toPresentation
end Composition
section Localization
variable {R} (r : R) [IsLocalization.Away r S]
noncomputable def localizationAway : SubmersivePresentation R S where
  __ := PreSubmersivePresentation.localizationAway S r
  jacobian_isUnit := by
    rw [localizationAway_jacobian]
    apply IsLocalization.map_units' (⟨r, 1, by simp⟩ : Submonoid.powers r)
  isFinite := Presentation.localizationAway_isFinite r
end Localization
section BaseChange
variable (T) [CommRing T] [Algebra R T] (P : SubmersivePresentation R S)
noncomputable def baseChange : SubmersivePresentation T (T ⊗[R] S) where
  toPreSubmersivePresentation := P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit := P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight
  isFinite := Presentation.baseChange_isFinite T P.toPresentation
end BaseChange
end Constructions
end SubmersivePresentation
class IsStandardSmooth : Prop where
  out : Nonempty (SubmersivePresentation.{t, w} R S)
noncomputable def IsStandardSmooth.relativeDimension [IsStandardSmooth R S] : ℕ :=
  ‹IsStandardSmooth R S›.out.some.dimension
class IsStandardSmoothOfRelativeDimension : Prop where
  out : ∃ P : SubmersivePresentation.{t, w} R S, P.dimension = n
variable {R} {S}
lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
    [IsStandardSmoothOfRelativeDimension.{t, w} n R S] :
    IsStandardSmooth.{t, w} R S :=
  ⟨‹IsStandardSmoothOfRelativeDimension n R S›.out.nonempty⟩
lemma IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
    (h : Function.Bijective (algebraMap R S)) :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 R S :=
  ⟨SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩
variable (R) in
instance IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 R R :=
  IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective Function.bijective_id
section Composition
variable (R S T) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
lemma IsStandardSmooth.trans [IsStandardSmooth.{t, w} R S] [IsStandardSmooth.{t', w'} S T] :
    IsStandardSmooth.{max t t', max w w'} R T where
  out := by
    obtain ⟨⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨Q.comp P⟩
lemma IsStandardSmoothOfRelativeDimension.trans [IsStandardSmoothOfRelativeDimension.{t, w} n R S]
    [IsStandardSmoothOfRelativeDimension.{t', w'} m S T] :
    IsStandardSmoothOfRelativeDimension.{max t t', max w w'} (m + n) R T where
  out := by
    obtain ⟨P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension
end Composition
lemma IsStandardSmooth.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmooth.{0, 0} R S where
  out := ⟨SubmersivePresentation.localizationAway S r⟩
lemma IsStandardSmoothOfRelativeDimension.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmoothOfRelativeDimension.{0, 0} 0 R S where
  out := ⟨SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩
section BaseChange
variable (T) [CommRing T] [Algebra R T]
instance IsStandardSmooth.baseChange [IsStandardSmooth.{t, w} R S] :
    IsStandardSmooth.{t, w} T (T ⊗[R] S) where
  out := by
    obtain ⟨⟨P⟩⟩ := ‹IsStandardSmooth R S›
    exact ⟨P.baseChange R S T⟩
instance IsStandardSmoothOfRelativeDimension.baseChange
    [IsStandardSmoothOfRelativeDimension.{t, w} n R S] :
    IsStandardSmoothOfRelativeDimension.{t, w} n T (T ⊗[R] S) where
  out := by
    obtain ⟨P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    exact ⟨P.baseChange R S T, hP⟩
end BaseChange
end Algebra