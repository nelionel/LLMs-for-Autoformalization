import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Generators
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.TensorProduct.MvPolynomial
universe t w u v
open TensorProduct MvPolynomial
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
@[nolint checkUnivs]
structure Algebra.Presentation extends Algebra.Generators.{w} R S where
  rels : Type t
  relation : rels → toGenerators.Ring
  span_range_relation_eq_ker :
    Ideal.span (Set.range relation) = toGenerators.ker
namespace Algebra.Presentation
variable {R S}
variable (P : Presentation.{t, w} R S)
@[simp]
lemma aeval_val_relation (i) : aeval P.val (P.relation i) = 0 := by
  rw [← RingHom.mem_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
  exact Ideal.subset_span ⟨i, rfl⟩
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.ker
def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) P.aeval_val_σ
@[simp]
lemma quotientEquiv_mk (p : P.Ring) : P.quotientEquiv p = algebraMap P.Ring S p :=
  rfl
@[simp]
lemma quotientEquiv_symm (x : S) : P.quotientEquiv.symm x = P.σ x :=
  rfl
noncomputable def dimension : ℕ :=
  Nat.card P.vars - Nat.card P.rels
class IsFinite (P : Presentation.{t, w} R S) : Prop where
  finite_vars : Finite P.vars
  finite_rels : Finite P.rels
attribute [instance] IsFinite.finite_vars IsFinite.finite_rels
lemma ideal_fg_of_isFinite [P.IsFinite] : P.ker.FG := by
  use (Set.finite_range P.relation).toFinset
  simp [span_range_relation_eq_ker]
instance [P.IsFinite] : FinitePresentation R P.Quotient :=
  FinitePresentation.quotient P.ideal_fg_of_isFinite
lemma finitePresentation_of_isFinite [P.IsFinite] :
    FinitePresentation R S :=
  FinitePresentation.equiv (P.quotientEquiv.restrictScalars R)
section Construction
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    Presentation.{t, w} R S where
  __ := Generators.ofSurjectiveAlgebraMap h.surjective
  rels := PEmpty
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [← RingHom.injective_iff_ker_eq_bot]
    show Function.Injective (aeval PEmpty.elim)
    rw [aeval_injective_iff_of_isEmpty]
    exact h.injective
instance ofBijectiveAlgebraMap_isFinite (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap.{t, w} h).IsFinite where
  finite_vars := inferInstanceAs (Finite PEmpty.{w + 1})
  finite_rels := inferInstanceAs (Finite PEmpty.{t + 1})
lemma ofBijectiveAlgebraMap_dimension (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).dimension = 0 := by
  show Nat.card PEmpty - Nat.card PEmpty = 0
  simp only [Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty, le_refl, tsub_eq_zero_of_le]
variable (R) in
noncomputable def id : Presentation.{t, w} R R := ofBijectiveAlgebraMap Function.bijective_id
instance : (id R).IsFinite := ofBijectiveAlgebraMap_isFinite (R := R) Function.bijective_id
lemma id_dimension : (Presentation.id R).dimension = 0 :=
  ofBijectiveAlgebraMap_dimension (R := R) Function.bijective_id
section Localization
variable (r : R) [IsLocalization.Away r S]
open IsLocalization.Away
private lemma span_range_relation_eq_ker_localizationAway :
    Ideal.span { C r * X () - 1 } =
      RingHom.ker (aeval (S₁ := S) (Generators.localizationAway r).val) := by
  have : aeval (S₁ := S) (Generators.localizationAway r).val =
      (mvPolynomialQuotientEquiv S r).toAlgHom.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {C r * X () - 1})) := by
    ext x
    simp only [Generators.localizationAway_vars, aeval_X, Generators.localizationAway_val,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk,
      Function.comp_apply]
    rw [IsLocalization.Away.mvPolynomialQuotientEquiv_apply, aeval_X]
  rw [this]
  erw [← RingHom.comap_ker]
  simp only [Generators.localizationAway_vars, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
    AlgEquiv.toAlgHom_toRingHom]
  show Ideal.span {C r * X () - 1} = Ideal.comap _ (RingHom.ker (mvPolynomialQuotientEquiv S r))
  simp [RingHom.ker_equiv, ← RingHom.ker_eq_comap_bot]
variable (S) in
@[simps relation, simps (config := .lemmasOnly) rels]
noncomputable def localizationAway : Presentation R S where
  toGenerators := Generators.localizationAway r
  rels := Unit
  relation _ := C r * X () - 1
  span_range_relation_eq_ker := by
    simp only [Generators.localizationAway_vars, Set.range_const]
    apply span_range_relation_eq_ker_localizationAway r
instance localizationAway_isFinite : (localizationAway S r).IsFinite where
  finite_vars := inferInstanceAs <| Finite Unit
  finite_rels := inferInstanceAs <| Finite Unit
instance : Fintype (localizationAway S r).rels :=
  inferInstanceAs (Fintype Unit)
@[simp]
lemma localizationAway_dimension_zero : (localizationAway S r).dimension = 0 := by
  simp [Presentation.dimension, localizationAway, Generators.localizationAway_vars]
end Localization
section BaseChange
variable (T) [CommRing T] [Algebra R T] (P : Presentation R S)
private lemma span_range_relation_eq_ker_baseChange :
    Ideal.span (Set.range fun i ↦ (MvPolynomial.map (algebraMap R T)) (P.relation i)) =
      RingHom.ker (aeval (R := T) (S₁ := T ⊗[R] S) P.baseChange.val) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x ⟨y, hy⟩
    have Z := aeval_val_relation P y
    apply_fun TensorProduct.includeRight (R := R) (A := T) at Z
    rw [map_zero] at Z
    simp only [SetLike.mem_coe, RingHom.mem_ker, ← Z, ← hy, algebraMap_apply,
      TensorProduct.includeRight_apply]
    erw [aeval_map_algebraMap]
    show _ = TensorProduct.includeRight _
    erw [map_aeval, TensorProduct.includeRight.comp_algebraMap]
    rfl
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have H := Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
      P.algebraMap_surjective
    let e := MvPolynomial.algebraTensorAlgEquiv (R := R) (σ := P.vars) (A := T)
    have H' : e.symm x ∈ RingHom.ker (TensorProduct.map (AlgHom.id R T)
        (IsScalarTower.toAlgHom R P.Ring S)) := by
      rw [RingHom.mem_ker, ← hx]
      clear hx
      induction x using MvPolynomial.induction_on with
      | h_C a =>
        simp only [Generators.algebraMap_apply, algHom_C, TensorProduct.algebraMap_apply,
          id.map_eq_id, RingHom.id_apply, e]
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
        simp only [TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply,
          TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one, algebraMap_eq]
        erw [aeval_C]
        simp
      | h_add p q hp hq => simp only [map_add, hp, hq]
      | h_X p i hp =>
        simp only [map_mul, algebraTensorAlgEquiv_symm_X, hp, TensorProduct.map_tmul, map_one,
          IsScalarTower.coe_toAlgHom', Generators.algebraMap_apply, aeval_X, e]
        congr
        erw [aeval_X]
        rw [Generators.baseChange_val]
    rw [H] at H'
    replace H' : e.symm x ∈ Ideal.map TensorProduct.includeRight P.ker := H'
    erw [← P.span_range_relation_eq_ker, ← Ideal.mem_comap, Ideal.comap_symm,
      Ideal.map_map, Ideal.map_span, ← Set.range_comp] at H'
    convert H'
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      TensorProduct.includeRight_apply, TensorProduct.lift_tmul, map_one, mapAlgHom_apply, one_mul]
    rfl
@[simps relation, simps (config := .lemmasOnly) rels]
noncomputable
def baseChange : Presentation T (T ⊗[R] S) where
  __ := Generators.baseChange P.toGenerators
  rels := P.rels
  relation i := MvPolynomial.map (algebraMap R T) (P.relation i)
  span_range_relation_eq_ker := P.span_range_relation_eq_ker_baseChange T
instance baseChange_isFinite [P.IsFinite] : (P.baseChange T).IsFinite where
  finite_vars := inferInstanceAs <| Finite (P.vars)
  finite_rels := inferInstanceAs <| Finite (P.rels)
end BaseChange
section Composition
variable {T} [CommRing T] [Algebra S T]
variable (Q : Presentation S T) (P : Presentation R S)
private noncomputable def aux : MvPolynomial (Q.vars ⊕ P.vars) R →ₐ[R] MvPolynomial Q.vars S :=
  aeval (Sum.elim X (MvPolynomial.C ∘ P.val))
private noncomputable def comp_relation_aux (r : Q.rels) : MvPolynomial (Q.vars ⊕ P.vars) R :=
  Finsupp.sum (Q.relation r)
    (fun x j ↦ (MvPolynomial.rename Sum.inr <| P.σ j) * monomial (x.mapDomain Sum.inl) 1)
@[simp]
private lemma aux_X (i : Q.vars ⊕ P.vars) : (Q.aux P) (X i) = Sum.elim X (C ∘ P.val) i :=
  aeval_X (Sum.elim X (C ∘ P.val)) i
private lemma comp_relation_aux_map (r : Q.rels) :
    (Q.aux P) (Q.comp_relation_aux P r) = Q.relation r := by
  simp only [aux, comp_relation_aux, Generators.comp_vars, Sum.elim_inl, map_finsupp_sum]
  simp only [_root_.map_mul, aeval_rename, aeval_monomial, Sum.elim_comp_inr]
  conv_rhs => rw [← Finsupp.sum_single (Q.relation r)]
  congr
  ext u s m
  simp only [MvPolynomial.single_eq_monomial, aeval, AlgHom.coe_mk, coe_eval₂Hom]
  rw [monomial_eq, IsScalarTower.algebraMap_eq R S, algebraMap_eq, ← eval₂_comp_left, ← aeval_def]
  simp [Finsupp.prod_mapDomain_index_inj (Sum.inl_injective)]
private lemma aux_surjective : Function.Surjective (Q.aux P) := fun p ↦ by
  induction' p using MvPolynomial.induction_on with a p q hp hq p i h
  · use rename Sum.inr <| P.σ a
    simp only [aux, aeval_rename, Sum.elim_comp_inr]
    have (p : MvPolynomial P.vars R) :
        aeval (C ∘ P.val) p = (C (aeval P.val p) : MvPolynomial Q.vars S) := by
      induction' p using MvPolynomial.induction_on with a p q hp hq p i h
      · simp
      · simp [hp, hq]
      · simp [h]
    simp [this]
  · obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  · obtain ⟨a, rfl⟩ := h
    exact ⟨(a * X (Sum.inl i)), by simp⟩
private lemma aux_image_relation :
    Q.aux P '' (Set.range (Algebra.Presentation.comp_relation_aux Q P)) = Set.range Q.relation := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (Q.comp_relation_aux_map P a).symm⟩
  · rintro ⟨y, rfl⟩
    use Q.comp_relation_aux P y
    simp only [Set.mem_range, exists_apply_eq_apply, true_and, comp_relation_aux_map]
private lemma aux_eq_comp : Q.aux P =
    (MvPolynomial.mapAlgHom (aeval P.val)).comp (sumAlgEquiv R Q.vars P.vars).toAlgHom := by
  ext i : 1
  cases i <;> simp
private lemma aux_ker :
    RingHom.ker (Q.aux P) = Ideal.map (rename Sum.inr) (RingHom.ker (aeval P.val)) := by
  rw [aux_eq_comp, ← AlgHom.comap_ker, MvPolynomial.ker_mapAlgHom]
  show Ideal.comap _ (Ideal.map (IsScalarTower.toAlgHom R (MvPolynomial P.vars R) _) _) = _
  rw [← sumAlgEquiv_comp_rename_inr, ← Ideal.map_mapₐ, Ideal.comap_map_of_bijective]
  simpa using AlgEquiv.bijective (sumAlgEquiv R Q.vars P.vars)
variable [Algebra R T] [IsScalarTower R S T]
private lemma aeval_comp_val_eq :
    (aeval (Q.comp P.toGenerators).val) =
      (aevalTower (IsScalarTower.toAlgHom R S T) Q.val).comp (Q.aux P) := by
  ext i
  simp only [AlgHom.coe_comp, Function.comp_apply]
  erw [Q.aux_X P i]
  cases i <;> simp
private lemma span_range_relation_eq_ker_comp : Ideal.span
    (Set.range (Sum.elim (Algebra.Presentation.comp_relation_aux Q P)
      fun rp ↦ (rename Sum.inr) (P.relation rp))) = (Q.comp P.toGenerators).ker := by
  rw [Generators.ker_eq_ker_aeval_val, Q.aeval_comp_val_eq, ← AlgHom.comap_ker]
  show _ = Ideal.comap _ (Q.ker)
  rw [← Q.span_range_relation_eq_ker, ← Q.aux_image_relation P, ← Ideal.map_span,
    Ideal.comap_map_of_surjective' _ (Q.aux_surjective P)]
  rw [Set.Sum.elim_range, Ideal.span_union, Q.aux_ker, ← P.ker_eq_ker_aeval_val,
    ← P.span_range_relation_eq_ker, Ideal.map_span]
  congr
  ext
  simp
@[simps rels, simps (config := .lemmasOnly) relation]
noncomputable def comp : Presentation R T where
  toGenerators := Q.toGenerators.comp P.toGenerators
  rels := Q.rels ⊕ P.rels
  relation := Sum.elim (Q.comp_relation_aux P)
    (fun rp ↦ MvPolynomial.rename Sum.inr <| P.relation rp)
  span_range_relation_eq_ker := Q.span_range_relation_eq_ker_comp P
@[simp]
lemma comp_relation_inr (r : P.rels) :
    (Q.comp P).relation (Sum.inr r) = rename Sum.inr (P.relation r) :=
  rfl
lemma comp_aeval_relation_inl (r : Q.rels) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val)) ((Q.comp P).relation (Sum.inl r)) =
      Q.relation r := by
  show (Q.aux P) _ = _
  simp [comp_relation, comp_relation_aux_map]
instance comp_isFinite [P.IsFinite] [Q.IsFinite] : (Q.comp P).IsFinite where
  finite_vars := inferInstanceAs <| Finite (Q.vars ⊕ P.vars)
  finite_rels := inferInstanceAs <| Finite (Q.rels ⊕ P.rels)
end Composition
end Construction
end Presentation
end Algebra