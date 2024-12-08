import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IsAdjoinRoot
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
open Ideal Polynomial DoubleQuot UniqueFactorizationMonoid Algebra RingHom
local notation:max R "<" x:max ">" => adjoin R ({x} : Set S)
def conductor (x : S) : Ideal S where
  carrier := {a | ∀ b : S, a * b ∈ R<x>}
  zero_mem' b := by simpa only [zero_mul] using Subalgebra.zero_mem _
  add_mem' ha hb c := by simpa only [add_mul] using Subalgebra.add_mem _ (ha c) (hb c)
  smul_mem' c a ha b := by simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * b)
variable {R} {x : S}
theorem conductor_eq_of_eq {y : S} (h : (R<x> : Set S) = R<y>) : conductor R x = conductor R y :=
  Ideal.ext fun _ => forall_congr' fun _ => Set.ext_iff.mp h _
theorem conductor_subset_adjoin : (conductor R x : Set S) ⊆ R<x> := fun y hy => by
  simpa only [mul_one] using hy 1
theorem mem_conductor_iff {y : S} : y ∈ conductor R x ↔ ∀ b : S, y * b ∈ R<x> :=
  ⟨fun h => h, fun h => h⟩
theorem conductor_eq_top_of_adjoin_eq_top (h : R<x> = ⊤) : conductor R x = ⊤ := by
  simp only [Ideal.eq_top_iff_one, mem_conductor_iff, h, mem_top, forall_const]
theorem conductor_eq_top_of_powerBasis (pb : PowerBasis R S) : conductor R pb.gen = ⊤ :=
  conductor_eq_top_of_adjoin_eq_top pb.adjoin_gen_eq_top
open IsLocalization in
lemma mem_coeSubmodule_conductor {L} [CommRing L] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [NoZeroSMulDivisors S L] {x : S} {y : L} :
    y ∈ coeSubmodule L (conductor R x) ↔ ∀ z : S,
      y * (algebraMap S L) z ∈ Algebra.adjoin R {algebraMap S L x} := by
  cases subsingleton_or_nontrivial L
  · rw [Subsingleton.elim (coeSubmodule L _) ⊤, Subsingleton.elim (Algebra.adjoin R _) ⊤]; simp
  trans ∀ z, y * (algebraMap S L) z ∈ (Algebra.adjoin R {x}).map (IsScalarTower.toAlgHom R S L)
  · simp only [coeSubmodule, Submodule.mem_map, Algebra.linearMap_apply, Subalgebra.mem_map,
      IsScalarTower.coe_toAlgHom']
    constructor
    · rintro ⟨y, hy, rfl⟩ z
      exact ⟨_, hy z, map_mul _ _ _⟩
    · intro H
      obtain ⟨y, _, e⟩ := H 1
      rw [map_one, mul_one] at e
      subst e
      simp only [← _root_.map_mul, (NoZeroSMulDivisors.algebraMap_injective S L).eq_iff,
        exists_eq_right] at H
      exact ⟨_, H, rfl⟩
  · rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
variable {I : Ideal R}
theorem prod_mem_ideal_map_of_mem_conductor {p : R} {z : S}
    (hp : p ∈ Ideal.comap (algebraMap R S) (conductor R x)) (hz' : z ∈ I.map (algebraMap R S)) :
    algebraMap R S p * z ∈ algebraMap R<x> S '' ↑(I.map (algebraMap R R<x>)) := by
  rw [Ideal.map, Ideal.span, Finsupp.mem_span_image_iff_linearCombination] at hz'
  obtain ⟨l, H, H'⟩ := hz'
  rw [Finsupp.linearCombination_apply] at H'
  rw [← H', mul_comm, Finsupp.sum_mul]
  have lem : ∀ {a : R}, a ∈ I → l a • algebraMap R S a * algebraMap R S p ∈
      algebraMap R<x> S '' I.map (algebraMap R R<x>) := by
    intro a ha
    rw [Algebra.id.smul_eq_mul, mul_assoc, mul_comm, mul_assoc, Set.mem_image]
    refine Exists.intro
        (algebraMap R R<x> a * ⟨l a * algebraMap R S p,
          show l a * algebraMap R S p ∈ R<x> from ?h⟩) ?_
    case h =>
      rw [mul_comm]
      exact mem_conductor_iff.mp (Ideal.mem_comap.mp hp) _
    · refine ⟨?_, ?_⟩
      · rw [mul_comm]
        apply Ideal.mul_mem_left (I.map (algebraMap R R<x>)) _ (Ideal.mem_map_of_mem _ ha)
      · simp only [RingHom.map_mul, mul_comm (algebraMap R S p) (l a)]
        rfl
  refine Finset.sum_induction _ (fun u => u ∈ algebraMap R<x> S '' I.map (algebraMap R R<x>))
      (fun a b => ?_) ?_ ?_
  · rintro ⟨z, hz, rfl⟩ ⟨y, hy, rfl⟩
    rw [← RingHom.map_add]
    exact ⟨z + y, Ideal.add_mem _ (SetLike.mem_coe.mp hz) hy, rfl⟩
  · exact ⟨0, SetLike.mem_coe.mpr <| Ideal.zero_mem _, RingHom.map_zero _⟩
  · intro y hy
    exact lem ((Finsupp.mem_supported _ l).mp H hy)
theorem comap_map_eq_map_adjoin_of_coprime_conductor
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (h_alg : Function.Injective (algebraMap R<x> S)) :
    (I.map (algebraMap R S)).comap (algebraMap R<x> S) = I.map (algebraMap R R<x>) := by
  apply le_antisymm
  · 
    intro y hy
    obtain ⟨z, hz⟩ := y
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hx)
    have temp : algebraMap R S p * z + algebraMap R S q * z = z := by
      simp only [← add_mul, ← RingHom.map_add (algebraMap R S), hpq, map_one, one_mul]
    suffices z ∈ algebraMap R<x> S '' I.map (algebraMap R R<x>) ↔
        (⟨z, hz⟩ : R<x>) ∈ I.map (algebraMap R R<x>) by
      rw [← this, ← temp]
      obtain ⟨a, ha⟩ := (Set.mem_image _ _ _).mp (prod_mem_ideal_map_of_mem_conductor hp
          (show z ∈ I.map (algebraMap R S) by rwa [Ideal.mem_comap] at hy))
      use a + algebraMap R R<x> q * ⟨z, hz⟩
      refine ⟨Ideal.add_mem (I.map (algebraMap R R<x>)) ha.left ?_, by
          simp only [ha.right, map_add, _root_.map_mul, add_right_inj]; rfl⟩
      rw [mul_comm]
      exact Ideal.mul_mem_left (I.map (algebraMap R R<x>)) _ (Ideal.mem_map_of_mem _ hq)
    refine ⟨fun h => ?_,
      fun h => (Set.mem_image _ _ _).mpr (Exists.intro ⟨z, hz⟩ ⟨by simp [h], rfl⟩)⟩
    obtain ⟨x₁, hx₁, hx₂⟩ := (Set.mem_image _ _ _).mp h
    have : x₁ = ⟨z, hz⟩ := by
      apply h_alg
      simp only [hx₂, algebraMap_eq_smul_one]
      rw [Submonoid.mk_smul, smul_eq_mul, mul_one]
    rwa [← this]
  · 
    have : algebraMap R S = (algebraMap _ S).comp (algebraMap R R<x>) := by ext; rfl
    rw [this, ← Ideal.map_map]
    apply Ideal.le_comap_map
noncomputable def quotAdjoinEquivQuotMap (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (h_alg : Function.Injective (algebraMap R<x> S)) :
    R<x> ⧸ I.map (algebraMap R R<x>) ≃+* S ⧸ I.map (algebraMap R S) := by
  let f : R<x> ⧸ I.map (algebraMap R R<x>) →+* S ⧸ I.map (algebraMap R S) :=
    (Ideal.Quotient.lift (I.map (algebraMap R R<x>))
      ((Ideal.Quotient.mk (I.map (algebraMap R S))).comp (algebraMap R<x> S)) (fun r hr => by
      have : algebraMap R S = (algebraMap R<x> S).comp (algebraMap R R<x>) := by ext; rfl
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, this, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hr))
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · 
    refine RingHom.lift_injective_of_ker_le_ideal _ _ fun u hu => ?_
    rwa [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
      comap_map_eq_map_adjoin_of_coprime_conductor hx h_alg] at hu
  · 
    refine Ideal.Quotient.lift_surjective_of_surjective _ _ fun y => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective y
    have : z ∈ conductor R x ⊔ I.map (algebraMap R S) := by
      suffices conductor R x ⊔ I.map (algebraMap R S) = ⊤ by simp only [this, Submodule.mem_top]
      rw [Ideal.eq_top_iff_one] at hx ⊢
      replace hx := Ideal.mem_map_of_mem (algebraMap R S) hx
      rw [Ideal.map_sup, RingHom.map_one] at hx
      exact (sup_le_sup
        (show ((conductor R x).comap (algebraMap R S)).map (algebraMap R S) ≤ conductor R x
          from Ideal.map_comap_le)
          (le_refl (I.map (algebraMap R S)))) hx
    rw [← Ideal.mem_quotient_iff_mem_sup, hz, Ideal.mem_map_iff_of_surjective] at this
    · obtain ⟨u, hu, hu'⟩ := this
      use ⟨u, conductor_subset_adjoin hu⟩
      simp only [← hu']
      rfl
    · exact Ideal.Quotient.mk_surjective
@[simp]
theorem quotAdjoinEquivQuotMap_apply_mk (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (h_alg : Function.Injective (algebraMap R<x> S)) (a : R<x>) :
    quotAdjoinEquivQuotMap hx h_alg (Ideal.Quotient.mk (I.map (algebraMap R R<x>)) a) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) ↑a := rfl
namespace KummerDedekind
open scoped Polynomial
variable [IsDomain R] [IsIntegrallyClosed R]
variable [IsDedekindDomain S]
variable [NoZeroSMulDivisors R S]
attribute [local instance] Ideal.Quotient.field
open Classical in
noncomputable def normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    {J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} := by
  have : IsPrincipalIdealRing (R ⧸ I)[X] := inferInstance
  let f : S ⧸ map (algebraMap R S) I ≃+*
    (R ⧸ I)[X] ⧸ span {Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)} := by
    refine (quotAdjoinEquivQuotMap hx ?_).symm.trans
      (((Algebra.adjoin.powerBasis'
        hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans (quotEquivOfEq ?_))
    · exact NoZeroSMulDivisors.algebraMap_injective (Algebra.adjoin R {x}) S
    · rw [Algebra.adjoin.powerBasis'_minpoly_gen hx']
  refine (normalizedFactorsEquivOfQuotEquiv f ?_ ?_).trans ?_
  · rwa [Ne, map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective R S), ← Ne]
  · by_contra h
    exact (show Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) ≠ 0 from
      Polynomial.map_monic_ne_zero (minpoly.monic hx')) (span_singleton_eq_bot.mp h)
  · refine (normalizedFactorsEquivSpanNormalizedFactors ?_).symm
    exact Polynomial.map_monic_ne_zero (minpoly.monic hx')
open Classical in
theorem emultiplicity_factors_map_eq_emultiplicity
    (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) {J : Ideal S}
    (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    emultiplicity J (I.map (algebraMap R S)) =
      emultiplicity (↑(normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' ⟨J, hJ⟩))
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk, Equiv.coe_trans, Function.comp_apply,
    emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity,
    normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity]
open Classical in
theorem normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f : Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach := by
  ext J
  by_cases hJ : J ∈ normalizedFactors (I.map (algebraMap R S))
  swap
  · rw [Multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [not_exists]
    rintro J' ⟨_, rfl⟩
    exact
      hJ ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J').prop
  have := emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ
  rw [emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_count_normalizedFactors,
    UniqueFactorizationMonoid.normalize_normalized_factor _ hJ,
    UniqueFactorizationMonoid.normalize_normalized_factor, Nat.cast_inj] at this
  · refine this.trans ?_
    generalize hJ' :
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx') ⟨J, hJ⟩ = J'
    have : ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J' : Ideal S) =
        J := by
      rw [← hJ', Equiv.symm_apply_apply _ _, Subtype.coe_mk]
    subst this
    rw [Multiset.count_map_eq_count' fun f =>
        ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f :
          Ideal S),
      Multiset.count_attach]
    · exact Subtype.coe_injective.comp (Equiv.injective _)
  · exact (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact irreducible_of_normalized_factor _
        (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact Polynomial.map_monic_ne_zero (minpoly.monic hx')
  · exact irreducible_of_normalized_factor _ hJ
  · rwa [← bot_eq_zero, Ne,
      map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective R S)]
theorem Ideal.irreducible_map_of_irreducible_minpoly (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
    (hf : Irreducible (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    Irreducible (I.map (algebraMap R S)) := by
  classical
  have mem_norm_factors : normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) ∈
      normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
    simp [normalizedFactors_irreducible hf]
  suffices ∃ y, normalizedFactors (I.map (algebraMap R S)) = {y} by
    obtain ⟨y, hy⟩ := this
    have h := normalizedFactors_prod (show I.map (algebraMap R S) ≠ 0 by
          rwa [← bot_eq_zero, Ne,
            map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective R S)])
    rw [associated_iff_eq, hy, Multiset.prod_singleton] at h
    rw [← h]
    exact
      irreducible_of_normalized_factor y
        (show y ∈ normalizedFactors (I.map (algebraMap R S)) by simp [hy])
  rw [normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx']
  use ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
        ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩ :
      Ideal S)
  rw [Multiset.map_eq_singleton]
  use ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩
  refine ⟨?_, rfl⟩
  apply Multiset.map_injective Subtype.coe_injective
  rw [Multiset.attach_map_val, Multiset.map_singleton, Subtype.coe_mk]
  exact normalizedFactors_irreducible hf
end KummerDedekind