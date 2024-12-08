import Mathlib.Algebra.DirectSum.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Basis.Defs
universe u v w u₁
namespace DirectSum
open DirectSum Finsupp
section General
variable {R : Type u} [Semiring R]
variable {ι : Type v}
variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
instance : Module R (⨁ i, M i) :=
  DFinsupp.module
instance {S : Type*} [Semiring S] [∀ i, Module S (M i)] [∀ i, SMulCommClass R S (M i)] :
    SMulCommClass R S (⨁ i, M i) :=
  DFinsupp.smulCommClass
instance {S : Type*} [Semiring S] [SMul R S] [∀ i, Module S (M i)] [∀ i, IsScalarTower R S (M i)] :
    IsScalarTower R S (⨁ i, M i) :=
  DFinsupp.isScalarTower
instance [∀ i, Module Rᵐᵒᵖ (M i)] [∀ i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i) :=
  DFinsupp.isCentralScalar
theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
  DFinsupp.smul_apply _ _ _
variable (R ι M)
section DecidableEq
variable [DecidableEq ι]
def lmk : ∀ s : Finset ι, (∀ i : (↑s : Set ι), M i.val) →ₗ[R] ⨁ i, M i :=
  DFinsupp.lmk
def lof : ∀ i : ι, M i →ₗ[R] ⨁ i, M i :=
  DFinsupp.lsingle
theorem lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b := rfl
variable {ι M}
theorem single_eq_lof (i : ι) (b : M i) : DFinsupp.single i b = lof R ι M i b := rfl
theorem mk_smul (s : Finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
  (lmk R ι M s).map_smul c x
theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
  (lof R ι M i).map_smul c x
variable {R}
theorem support_smul [∀ (i : ι) (x : M i), Decidable (x ≠ 0)] (c : R) (v : ⨁ i, M i) :
    (c • v).support ⊆ v.support :=
  DFinsupp.support_smul _ _
variable {N : Type u₁} [AddCommMonoid N] [Module R N]
variable (φ : ∀ i, M i →ₗ[R] N)
variable (R ι N)
def toModule : (⨁ i, M i) →ₗ[R] N :=
  DFunLike.coe (DFinsupp.lsum ℕ) φ
theorem coe_toModule_eq_coe_toAddMonoid :
    (toModule R ι N φ : (⨁ i, M i) → N) = toAddMonoid fun i ↦ (φ i).toAddMonoidHom := rfl
variable {ι N φ}
@[simp]
theorem toModule_lof (i) (x : M i) : toModule R ι N φ (lof R ι M i x) = φ i x :=
  toAddMonoid_of (fun i ↦ (φ i).toAddMonoidHom) i x
variable (ψ : (⨁ i, M i) →ₗ[R] N)
theorem toModule.unique (f : ⨁ i, M i) : ψ f = toModule R ι N (fun i ↦ ψ.comp <| lof R ι M i) f :=
  toAddMonoid.unique ψ.toAddMonoidHom f
variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}
@[ext]
theorem linearMap_ext ⦃ψ ψ' : (⨁ i, M i) →ₗ[R] N⦄
    (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ' :=
  DFinsupp.lhom_ext' H
def lsetToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, M i) →ₗ[R] ⨁ i : T, M i :=
  toModule R _ _ fun i ↦ lof R T (fun i : Subtype T ↦ M i) ⟨i, H i.prop⟩
variable (ι M)
@[simps apply]
def linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] ∀ i, M i :=
  { DFinsupp.equivFunOnFintype with
    toFun := (↑)
    map_add' := fun f g ↦ by
      ext
      rw [add_apply, Pi.add_apply]
    map_smul' := fun c f ↦ by
      simp_rw [RingHom.id_apply]
      rw [DFinsupp.coe_smul] }
variable {ι M}
@[simp]
theorem linearEquivFunOnFintype_lof [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M) (lof R ι M i m) = Pi.single i m := by
  ext a
  change (DFinsupp.equivFunOnFintype (lof R ι M i m)) a = _
  convert _root_.congr_fun (DFinsupp.equivFunOnFintype_single i m) a
@[simp]
theorem linearEquivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M).symm (Pi.single i m) = lof R ι M i m := by
  change (DFinsupp.equivFunOnFintype.symm (Pi.single i m)) = _
  rw [DFinsupp.equivFunOnFintype_symm_single i m]
  rfl
end DecidableEq
@[simp]
theorem linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) :
    (linearEquivFunOnFintype R ι M).symm f = f := by
  simp [linearEquivFunOnFintype]
protected def lid (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Module R M] [Unique ι] :
    (⨁ _ : ι, M) ≃ₗ[R] M :=
  { DirectSum.id M ι, toModule R ι M fun _ ↦ LinearMap.id with }
def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
  DFinsupp.lapply i
variable {ι M}
theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = component R ι M i f := rfl
@[ext (iff := false)]
theorem ext {f g : ⨁ i, M i} (h : ∀ i, component R ι M i f = component R ι M i g) : f = g :=
  DFinsupp.ext h
theorem ext_iff {f g : ⨁ i, M i} : f = g ↔ ∀ i, component R ι M i f = component R ι M i g :=
  ⟨fun h _ ↦ by rw [h], ext R⟩
@[simp]
theorem lof_apply [DecidableEq ι] (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
  DFinsupp.single_eq_same
@[simp]
theorem component.lof_self [DecidableEq ι] (i : ι) (b : M i) :
    component R ι M i ((lof R ι M i) b) = b :=
  lof_apply R i b
theorem component.of [DecidableEq ι] (i j : ι) (b : M j) :
    component R ι M i ((lof R ι M j) b) = if h : j = i then Eq.recOn h b else 0 :=
  DFinsupp.single_apply
section CongrLeft
variable {κ : Type*}
def lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k) :=
  { equivCongrLeft h with map_smul' := DFinsupp.comapDomain'_smul h.invFun h.right_inv }
@[simp]
theorem lequivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) :
    lequivCongrLeft R h f k = f (h.symm k) :=
  equivCongrLeft_apply _ _ _
end CongrLeft
section Sigma
variable {α : ι → Type*} {δ : ∀ i, α i → Type w}
variable [DecidableEq ι] [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)]
def sigmaLcurry : (⨁ i : Σ_, _, δ i.1 i.2) →ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurry with map_smul' := fun r ↦ by convert DFinsupp.sigmaCurry_smul (δ := δ) r }
@[simp]
theorem sigmaLcurry_apply (f : ⨁ i : Σ_, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaLcurry R f i j = f ⟨i, j⟩ :=
  sigmaCurry_apply f i j
def sigmaLuncurry : (⨁ (i) (j), δ i j) →ₗ[R] ⨁ i : Σ_, _, δ i.1 i.2 :=
  { sigmaUncurry with map_smul' := DFinsupp.sigmaUncurry_smul }
@[simp]
theorem sigmaLuncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaLuncurry R f ⟨i, j⟩ = f i j :=
  sigmaUncurry_apply f i j
def sigmaLcurryEquiv : (⨁ i : Σ_, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurryEquiv, sigmaLcurry R with }
end Sigma
section Option
variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)] [∀ i, Module R (α i)]
@[simps]
noncomputable def lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i) :=
  { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }
end Option
end General
section Submodule
section Semiring
variable {R : Type u} [Semiring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (A : ι → Submodule R M)
def coeLinearMap : (⨁ i, A i) →ₗ[R] M :=
  toModule R ι M fun i ↦ (A i).subtype
theorem coeLinearMap_eq_dfinsupp_sum [DecidableEq M] (x : DirectSum ι fun i => A i) :
    coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [coeLinearMap, toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]
@[simp]
theorem coeLinearMap_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i ↦ A i) i x) = x :=
  toAddMonoid_of (β := fun i => A i) (fun i ↦ ((A i).subtype : A i →+ M)) i x
variable {A}
theorem range_coeLinearMap : LinearMap.range (coeLinearMap A) = ⨆ i, A i :=
  (Submodule.iSup_eq_range_dfinsupp_lsum _).symm
@[simp]
theorem IsInternal.ofBijective_coeLinearMap_same (h : IsInternal A)
    {i : ι} (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = x := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_same]
@[simp]
theorem IsInternal.ofBijective_coeLinearMap_of_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_of_ne i j _ hij]
theorem IsInternal.ofBijective_coeLinearMap_of_mem (h : IsInternal A)
    {i : ι} {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = ⟨x, hx⟩ :=
  h.ofBijective_coeLinearMap_same ⟨x, hx⟩
theorem IsInternal.ofBijective_coeLinearMap_of_mem_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 :=
  h.ofBijective_coeLinearMap_of_ne hij ⟨x, hx⟩
theorem IsInternal.submodule_iSup_eq_top (h : IsInternal A) : iSup A = ⊤ := by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.range_eq_top]
  exact Function.Bijective.surjective h
theorem IsInternal.submodule_iSupIndep (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_lsum_injective _ h.injective
@[deprecated (since := "2024-11-24")]
alias IsInternal.submodule_independent := IsInternal.submodule_iSupIndep
noncomputable def IsInternal.collectedBasis (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : Basis (Σi, α i) R M where
  repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i ↦ (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm
@[simp]
theorem IsInternal.collectedBasis_coe (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : ⇑(h.collectedBasis v) = fun a : Σi, α i ↦ ↑(v a.1 a.2) := by
  funext a
  simp only [IsInternal.collectedBasis, coeLinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, sigmaFinsuppLequivDFinsupp_apply,
    sigmaFinsuppEquivDFinsupp_single, LinearEquiv.ofBijective_apply,
    sigmaFinsuppAddEquivDFinsupp_apply]
  rw [DFinsupp.mapRange.linearEquiv_symm]
  erw [DFinsupp.mapRange.linearEquiv_apply]
  simp only [DFinsupp.mapRange_single, Basis.repr_symm_apply, linearCombination_single, one_smul,
    toModule]
  erw [DFinsupp.lsum_single]
  simp only [Submodule.coe_subtype]
theorem IsInternal.collectedBasis_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) (a : Σi, α i) : h.collectedBasis v a ∈ A a.1 := by simp
theorem IsInternal.collectedBasis_repr_of_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i : ι} {a : α i} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨i, a⟩ = (v i).repr ⟨x, hx⟩ a := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem hx]
theorem IsInternal.collectedBasis_repr_of_mem_ne (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i j : ι} (hij : i ≠ j) {a : α j} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨j, a⟩ = 0 := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]
theorem IsInternal.isCompl {A : ι → Submodule R M} {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) (hi : IsInternal A) : IsCompl (A i) (A j) :=
  ⟨hi.submodule_iSupIndep.pairwiseDisjoint hij,
    codisjoint_iff.mpr <| Eq.symm <| hi.submodule_iSup_eq_top.symm.trans <| by
      rw [← sSup_pair, iSup, ← Set.image_univ, h, Set.image_insert_eq, Set.image_singleton]⟩
end Semiring
section Ring
variable {R : Type u} [Ring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
theorem isInternal_submodule_of_iSupIndep_of_iSup_eq_top {A : ι → Submodule R M}
    (hi : iSupIndep A) (hs : iSup A = ⊤) : IsInternal A :=
  ⟨hi.dfinsupp_lsum_injective,
    (LinearMap.range_eq_top (f := DFinsupp.lsum _ _)).1 <|
      (Submodule.iSup_eq_range_dfinsupp_lsum _).symm.trans hs⟩
@[deprecated (since := "2024-11-24")]
alias isInternal_submodule_of_independent_of_iSup_eq_top :=
  isInternal_submodule_of_iSupIndep_of_iSup_eq_top
theorem isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι → Submodule R M) :
    IsInternal A ↔ iSupIndep A ∧ iSup A = ⊤ :=
  ⟨fun i ↦ ⟨i.submodule_iSupIndep, i.submodule_iSup_eq_top⟩,
    And.rec isInternal_submodule_of_iSupIndep_of_iSup_eq_top⟩
@[deprecated (since := "2024-11-24")]
alias isInternal_submodule_iff_independent_and_iSup_eq_top :=
  isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
theorem isInternal_submodule_iff_isCompl (A : ι → Submodule R M) {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) : IsInternal A ↔ IsCompl (A i) (A j) := by
  have : ∀ k, k = i ∨ k = j := fun k ↦ by simpa using Set.ext_iff.mp h k
  rw [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, iSup, ← Set.image_univ, h,
    Set.image_insert_eq, Set.image_singleton, sSup_pair, iSupIndep_pair hij this]
  exact ⟨fun ⟨hd, ht⟩ ↦ ⟨hd, codisjoint_iff.mpr ht⟩, fun ⟨hd, ht⟩ ↦ ⟨hd, ht.eq_top⟩⟩
@[simp]
theorem isInternal_ne_bot_iff {A : ι → Submodule R M} :
    IsInternal (fun i : {i // A i ≠ ⊥} ↦ A i) ↔ IsInternal A := by
  simp [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
lemma isInternal_biSup_submodule_of_iSupIndep {A : ι → Submodule R M} (s : Set ι)
    (h : iSupIndep <| fun i : s ↦ A i) :
    IsInternal <| fun (i : s) ↦ (A i).comap (⨆ i ∈ s, A i).subtype := by
  refine (isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, by simp [iSup_subtype]⟩
  let p := ⨆ i ∈ s, A i
  have hp : ∀ i ∈ s, A i ≤ p := fun i hi ↦ le_biSup A hi
  let e : Submodule R p ≃o Set.Iic p := p.mapIic
  suffices (e ∘ fun i : s ↦ (A i).comap p.subtype) = fun i ↦ ⟨A i, hp i i.property⟩ by
    rw [← iSupIndep_map_orderIso_iff e, this]
    exact .of_coe_Iic_comp h
  ext i m
  change m ∈ ((A i).comap p.subtype).map p.subtype ↔ _
  rw [Submodule.map_comap_subtype, inf_of_le_right (hp i i.property)]
@[deprecated (since := "2024-11-24")]
alias isInternal_biSup_submodule_of_independent := isInternal_biSup_submodule_of_iSupIndep
theorem IsInternal.addSubmonoid_iSupIndep {M : Type*} [AddCommMonoid M] {A : ι → AddSubmonoid M}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_sumAddHom_injective _ h.injective
@[deprecated (since := "2024-11-24")]
alias IsInternal.addSubmonoid_independent := IsInternal.addSubmonoid_iSupIndep
theorem IsInternal.addSubgroup_iSupIndep {G : Type*} [AddCommGroup G] {A : ι → AddSubgroup G}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_sumAddHom_injective' _ h.injective
@[deprecated (since := "2024-11-24")]
alias IsInternal.addSubgroup_independent := IsInternal.addSubgroup_iSupIndep
end Ring
end Submodule
end DirectSum