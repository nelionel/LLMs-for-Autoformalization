import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.SimpleModule
open Set Function Polynomial
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace Module.End
section CommRing
variable (f : End R M)
def IsSemisimple := IsSemisimpleModule R[X] (AEval' f)
def IsFinitelySemisimple : Prop :=
  ∀ p (hp : p ∈ invtSubmodule f), Module.Finite R p → IsSemisimple (LinearMap.restrict f hp)
variable {f}
lemma isSemisimple_iff' :
    f.IsSemisimple ↔ ∀ p : invtSubmodule f, ∃ q : invtSubmodule f, IsCompl p q := by
  rw [IsSemisimple, IsSemisimpleModule, (AEval.mapSubmodule R M f).symm.complementedLattice_iff,
    complementedLattice_iff]
  rfl
lemma isSemisimple_iff :
    f.IsSemisimple ↔ ∀ p ∈ invtSubmodule f, ∃ q ∈ invtSubmodule f, IsCompl p q := by
  simp_rw [isSemisimple_iff']
  aesop
lemma isSemisimple_restrict_iff (p) (hp : p ∈ invtSubmodule f) :
    IsSemisimple (LinearMap.restrict f hp) ↔
    ∀ q ∈ f.invtSubmodule, q ≤ p → ∃ r ≤ p, r ∈ f.invtSubmodule ∧ Disjoint q r ∧ q ⊔ r = p := by
  let e : Submodule R[X] (AEval' (f.restrict hp)) ≃o Iic (AEval.mapSubmodule R M f ⟨p, hp⟩) :=
    (Submodule.orderIsoMapComap <| AEval.restrict_equiv_mapSubmodule f p hp).trans
      (Submodule.mapIic _)
  simp_rw [IsSemisimple, IsSemisimpleModule, e.complementedLattice_iff, disjoint_iff,
    ← (OrderIso.Iic _ _).complementedLattice_iff, Iic.complementedLattice_iff, Subtype.forall,
    Subtype.exists, Subtype.mk_le_mk, Sublattice.mk_inf_mk, Sublattice.mk_sup_mk, Subtype.mk.injEq,
    exists_and_left, exists_and_right, invtSubmodule.mk_eq_bot_iff, exists_prop, and_assoc]
  rfl
lemma isFinitelySemisimple_iff' :
    f.IsFinitelySemisimple ↔ ∀ p (hp : p ∈ invtSubmodule f),
      Module.Finite R p → IsSemisimple (LinearMap.restrict f hp) :=
  Iff.rfl
lemma isFinitelySemisimple_iff :
    f.IsFinitelySemisimple ↔ ∀ p ∈ invtSubmodule f, Module.Finite R p → ∀ q ∈ invtSubmodule f,
      q ≤ p → ∃ r, r ≤ p ∧ r ∈ invtSubmodule f ∧ Disjoint q r ∧ q ⊔ r = p := by
  simp_rw [isFinitelySemisimple_iff', isSemisimple_restrict_iff]
@[simp]
lemma isSemisimple_zero [IsSemisimpleModule R M] : IsSemisimple (0 : Module.End R M) := by
  simpa [isSemisimple_iff] using exists_isCompl
@[simp]
lemma isSemisimple_id [IsSemisimpleModule R M] : IsSemisimple (LinearMap.id : Module.End R M) := by
  simpa [isSemisimple_iff] using exists_isCompl
@[simp] lemma isSemisimple_neg : (-f).IsSemisimple ↔ f.IsSemisimple := by
  simp [isSemisimple_iff, mem_invtSubmodule]
variable (f) in
protected lemma _root_.LinearEquiv.isSemisimple_iff {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    (g : End R M₂) (e : M ≃ₗ[R] M₂) (he : e ∘ₗ f = g ∘ₗ e) :
    f.IsSemisimple ↔ g.IsSemisimple := by
  let e : AEval' f ≃ₗ[R[X]] AEval' g := LinearEquiv.ofAEval _ (e.trans (AEval'.of g)) fun x ↦ by
    simpa [AEval'.X_smul_of] using LinearMap.congr_fun he x
  exact (Submodule.orderIsoMapComap e).complementedLattice_iff
lemma eq_zero_of_isNilpotent_isSemisimple (hn : IsNilpotent f) (hs : f.IsSemisimple) : f = 0 := by
  have ⟨n, h0⟩ := hn
  rw [← aeval_X (R := R) f]; rw [← aeval_X_pow (R := R) f] at h0
  rw [← RingHom.mem_ker, ← AEval.annihilator_eq_ker_aeval (M := M)] at h0 ⊢
  exact hs.annihilator_isRadical _ _ ⟨n, h0⟩
lemma eq_zero_of_isNilpotent_of_isFinitelySemisimple
    (hn : IsNilpotent f) (hs : IsFinitelySemisimple f) : f = 0 := by
  have (p) (hp₁ : p ∈ f.invtSubmodule) (hp₂ : Module.Finite R p) : f.restrict hp₁ = 0 := by
    specialize hs p hp₁ hp₂
    replace hn : IsNilpotent (f.restrict hp₁) := isNilpotent.restrict hp₁ hn
    exact eq_zero_of_isNilpotent_isSemisimple hn hs
  ext x
  obtain ⟨k : ℕ, hk : f ^ k = 0⟩ := hn
  let p := Submodule.span R {(f ^ i) x | (i : ℕ) (_ : i ≤ k)}
  have hp₁ : p ∈ f.invtSubmodule := by
    simp only [mem_invtSubmodule, p, Submodule.span_le]
    rintro - ⟨i, hi, rfl⟩
    apply Submodule.subset_span
    rcases lt_or_eq_of_le hi with hik | rfl
    · exact ⟨i + 1, hik, by simpa [LinearMap.pow_apply] using iterate_succ_apply' f i x⟩
    · exact ⟨i, by simp [hk]⟩
  have hp₂ : Module.Finite R p := by
    let g : ℕ → M := fun i ↦ (f ^ i) x
    have hg : {(f ^ i) x | (i : ℕ) (_ : i ≤ k)} = g '' Iic k := by ext; simp [g]
    exact Module.Finite.span_of_finite _ <| hg ▸ toFinite (g '' Iic k)
  simpa [LinearMap.restrict_apply, Subtype.ext_iff] using
    LinearMap.congr_fun (this p hp₁ hp₂) ⟨x, Submodule.subset_span ⟨0, k.zero_le, rfl⟩⟩
@[simp]
lemma isSemisimple_sub_algebraMap_iff {μ : R} :
    (f - algebraMap R (End R M) μ).IsSemisimple ↔ f.IsSemisimple := by
  suffices ∀ p : Submodule R M, p ≤ p.comap (f - algebraMap R (Module.End R M) μ) ↔ p ≤ p.comap f by
    simp [mem_invtSubmodule, isSemisimple_iff, this]
  refine fun p ↦ ⟨fun h x hx ↦ ?_, fun h x hx ↦ p.sub_mem (h hx) (p.smul_mem μ hx)⟩
  simpa using p.add_mem (h hx) (p.smul_mem μ hx)
lemma IsSemisimple.restrict {p : Submodule R M} (hp : p ∈ f.invtSubmodule) (hf : f.IsSemisimple) :
    IsSemisimple (f.restrict hp) := by
  rw [IsSemisimple] at hf ⊢
  let e : Submodule R[X] (AEval' (LinearMap.restrict f hp)) ≃o
      Iic (AEval.mapSubmodule R M f ⟨p, hp⟩) :=
    (Submodule.orderIsoMapComap <| AEval.restrict_equiv_mapSubmodule f p hp).trans <|
      Submodule.mapIic _
  exact e.complementedLattice_iff.mpr inferInstance
lemma IsSemisimple.isFinitelySemisimple (hf : f.IsSemisimple) :
    f.IsFinitelySemisimple :=
  isFinitelySemisimple_iff'.mp fun _ _ _ ↦ hf.restrict _
@[simp]
lemma isFinitelySemisimple_iff_isSemisimple [Module.Finite R M] :
    f.IsFinitelySemisimple ↔ f.IsSemisimple := by
  refine ⟨fun hf ↦ isSemisimple_iff.mpr fun p hp ↦ ?_, IsSemisimple.isFinitelySemisimple⟩
  obtain ⟨q, -, hq₁, hq₂, hq₃⟩ :=
    isFinitelySemisimple_iff.mp hf ⊤ (invtSubmodule.top_mem f) inferInstance p hp le_top
  exact ⟨q, hq₁, hq₂, codisjoint_iff.mpr hq₃⟩
@[simp]
lemma isFinitelySemisimple_sub_algebraMap_iff {μ : R} :
    (f - algebraMap R (End R M) μ).IsFinitelySemisimple ↔ f.IsFinitelySemisimple := by
  suffices ∀ p : Submodule R M, p ≤ p.comap (f - algebraMap R (Module.End R M) μ) ↔ p ≤ p.comap f by
    simp_rw [isFinitelySemisimple_iff, mem_invtSubmodule, this]
  refine fun p ↦ ⟨fun h x hx ↦ ?_, fun h x hx ↦ p.sub_mem (h hx) (p.smul_mem μ hx)⟩
  simpa using p.add_mem (h hx) (p.smul_mem μ hx)
lemma IsFinitelySemisimple.restrict {p : Submodule R M} (hp : p ∈ f.invtSubmodule)
    (hf : f.IsFinitelySemisimple) :
    IsFinitelySemisimple (f.restrict hp) := by
  intro q hq₁ hq₂
  have := invtSubmodule.map_subtype_mem_of_mem_invtSubmodule f hp hq₁
  let e : q ≃ₗ[R] q.map p.subtype := p.equivSubtypeMap q
  rw [e.isSemisimple_iff ((LinearMap.restrict f hp).restrict hq₁) (LinearMap.restrict f this) rfl]
  exact hf _ this (Finite.map q p.subtype)
end CommRing
section field
variable {K : Type*} [Field K] [Module K M] {f g : End K M}
lemma IsSemisimple_smul_iff {t : K} (ht : t ≠ 0) :
    (t • f).IsSemisimple ↔ f.IsSemisimple := by
  simp [isSemisimple_iff, mem_invtSubmodule, Submodule.comap_smul f (h := ht)]
lemma IsSemisimple_smul (t : K) (h : f.IsSemisimple) :
    (t • f).IsSemisimple := by
  wlog ht : t ≠ 0; · simp [not_not.mp ht]
  rwa [IsSemisimple_smul_iff ht]
theorem isSemisimple_of_squarefree_aeval_eq_zero {p : K[X]}
    (hp : Squarefree p) (hpf : aeval f p = 0) : f.IsSemisimple := by
  rw [← RingHom.mem_ker, ← AEval.annihilator_eq_ker_aeval (M := M), mem_annihilator,
      ← IsTorsionBy, ← isTorsionBySet_singleton_iff, isTorsionBySet_iff_is_torsion_by_span] at hpf
  let R := K[X] ⧸ Ideal.span {p}
  have : IsReduced R :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_iff_span_singleton.mp hp.isRadical)
  have : FiniteDimensional K R := (AdjoinRoot.powerBasis hp.ne_zero).finite
  have : IsArtinianRing R := .of_finite K R
  have : IsSemisimpleRing R := IsArtinianRing.isSemisimpleRing_of_isReduced R
  letI : Module R (AEval' f) := Module.IsTorsionBySet.module hpf
  let e : AEval' f →ₛₗ[Ideal.Quotient.mk (Ideal.span {p})] AEval' f :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  exact (e.isSemisimpleModule_iff_of_bijective bijective_id).mpr inferInstance
variable [FiniteDimensional K M]
section
variable (hf : f.IsSemisimple)
include hf
theorem IsSemisimple.minpoly_squarefree : Squarefree (minpoly K f) :=
  IsRadical.squarefree (minpoly.ne_zero <| Algebra.IsIntegral.isIntegral _) <| by
    rw [isRadical_iff_span_singleton, span_minpoly_eq_annihilator]; exact hf.annihilator_isRadical
protected theorem IsSemisimple.aeval (p : K[X]) : (aeval f p).IsSemisimple :=
  let R := K[X] ⧸ Ideal.span {minpoly K f}
  have : Module.Finite K R :=
    (AdjoinRoot.powerBasis' <| minpoly.monic <| Algebra.IsIntegral.isIntegral f).finite
  have : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).mp <|
    span_minpoly_eq_annihilator K f ▸ hf.annihilator_isRadical
  isSemisimple_of_squarefree_aeval_eq_zero ((minpoly.isRadical K _).squarefree <|
    minpoly.ne_zero <| .of_finite K <| Ideal.Quotient.mkₐ K (.span {minpoly K f}) p) <| by
      rw [← Ideal.Quotient.liftₐ_comp (.span {minpoly K f}) (aeval f)
        fun a h ↦ by rwa [Ideal.span, ← minpoly.ker_aeval_eq_span_minpoly] at h, aeval_algHom,
        AlgHom.comp_apply, AlgHom.comp_apply, ← aeval_algHom_apply, minpoly.aeval, map_zero]
theorem IsSemisimple.of_mem_adjoin_singleton {a : End K M}
    (ha : a ∈ Algebra.adjoin K {f}) : a.IsSemisimple := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha; obtain ⟨p, rfl⟩ := ha; exact .aeval hf _
protected theorem IsSemisimple.pow (n : ℕ) : (f ^ n).IsSemisimple :=
  .of_mem_adjoin_singleton hf (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)
end
section PerfectField
variable [PerfectField K] (comm : Commute f g) (hf : f.IsSemisimple) (hg : g.IsSemisimple)
include comm hf hg
attribute [local simp] Submodule.Quotient.quot_mk_eq_mk in
theorem IsSemisimple.of_mem_adjoin_pair {a : End K M} (ha : a ∈ Algebra.adjoin K {f, g}) :
    a.IsSemisimple := by
  let R := K[X] ⧸ Ideal.span {minpoly K f}
  let S := AdjoinRoot ((minpoly K g).map <| algebraMap K R)
  have : Module.Finite K R :=
    (AdjoinRoot.powerBasis' <| minpoly.monic <| Algebra.IsIntegral.isIntegral f).finite
  have : Module.Finite R S :=
    (AdjoinRoot.powerBasis' <| (minpoly.monic <| Algebra.IsIntegral.isIntegral g).map _).finite
  #adaptation_note
  set_option maxSynthPendingDepth 2 in
  have : IsScalarTower K R S := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite K S := .trans R S
  have : IsArtinianRing R := .of_finite K R
  have : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).mp <|
    span_minpoly_eq_annihilator K f ▸ hf.annihilator_isRadical
  have : IsReduced S := by
    simp_rw [S, AdjoinRoot, ← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    exact (PerfectField.separable_iff_squarefree.mpr hg.minpoly_squarefree).map.squarefree.isRadical
  let φ : S →ₐ[K] End K M := Ideal.Quotient.liftₐ _ (eval₂AlgHom' (Ideal.Quotient.liftₐ _ (aeval f)
    fun a ↦ ?_) g ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_ : _ ≤ RingHom.ker _)
  rotate_left 1
  · rw [Ideal.span, ← minpoly.ker_aeval_eq_span_minpoly]; exact id
  · rintro ⟨p⟩; exact p.induction_on (fun k ↦ by simp [R, Algebra.commute_algebraMap_left])
      (fun p q hp hq ↦ by simpa using hp.add_left hq)
      fun n k ↦ by simpa [R, pow_succ, ← mul_assoc _ _ X] using (·.mul_left comm)
  · simpa only [RingHom.mem_ker, eval₂AlgHom'_apply, eval₂_map, AlgHom.comp_algebraMap_of_tower]
      using minpoly.aeval K g
  have : Algebra.adjoin K {f, g} ≤ φ.range := Algebra.adjoin_le fun x ↦ by
    rintro (hx | hx) <;> rw [hx]
    · exact ⟨AdjoinRoot.of _ (AdjoinRoot.root _), (eval₂_C _ _).trans (aeval_X f)⟩
    · exact ⟨AdjoinRoot.root _, eval₂_X _ _⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp (this ha)
  refine isSemisimple_of_squarefree_aeval_eq_zero
    ((minpoly.isRadical K p).squarefree <| minpoly.ne_zero <| .of_finite K p) ?_
  rw [aeval_algHom, φ.comp_apply, minpoly.aeval, map_zero]
theorem IsSemisimple.add_of_commute : (f + g).IsSemisimple := .of_mem_adjoin_pair
  comm hf hg <| add_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)
theorem IsSemisimple.sub_of_commute : (f - g).IsSemisimple := .of_mem_adjoin_pair
  comm hf hg <| sub_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)
theorem IsSemisimple.mul_of_commute : (f * g).IsSemisimple := .of_mem_adjoin_pair
  comm hf hg <| mul_mem (Algebra.subset_adjoin <| .inl rfl) (Algebra.subset_adjoin <| .inr rfl)
end PerfectField
end field
end Module.End