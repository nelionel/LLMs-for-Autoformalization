import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
namespace MulChar
lemma eq_iff {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] {g : Rˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (χ₁ χ₂ : MulChar R R') :
    χ₁ = χ₂ ↔ χ₁ g.val = χ₂ g.val := by
  rw [← Equiv.apply_eq_iff_eq equivToUnitHom, MonoidHom.eq_iff_eq_on_generator hg,
    ← coe_equivToUnitHom, ← coe_equivToUnitHom, Units.ext_iff]
section Ring
variable {R R' : Type*} [CommRing R] [CommRing R']
@[simps!]
def starComp [StarRing R'] (χ : MulChar R R') : MulChar R R' :=
  χ.ringHomComp (starRingEnd R')
instance instStarMul [StarRing R'] : StarMul (MulChar R R') where
  star := starComp
  star_involutive χ := by
    ext1
    simp only [starComp_apply, RingHomCompTriple.comp_apply, RingHom.id_apply]
  star_mul χ χ' := by
    ext1
    simp only [starComp_apply, starRingEnd, coeToFun_mul, Pi.mul_apply, map_mul, RingHom.coe_coe,
      starRingAut_apply, mul_comm]
@[simp]
lemma star_apply [StarRing R'] (χ : MulChar R R') (a : R) : (star χ) a = star (χ a) :=
  rfl
lemma apply_mem_rootsOfUnity [Fintype Rˣ] (a : Rˣ) {χ : MulChar R R'} :
    equivToUnitHom χ a ∈ rootsOfUnity (Fintype.card Rˣ) R' := by
  rw [mem_rootsOfUnity, ← map_pow, ← (equivToUnitHom χ).map_one, pow_card_eq_one]
variable [Finite Rˣ]
open Complex in
lemma star_eq_inv (χ : MulChar R ℂ) : star χ = χ⁻¹ := by
  cases nonempty_fintype Rˣ
  ext1 a
  simp only [inv_apply_eq_inv']
  exact (inv_eq_conj <| norm_eq_one_of_mem_rootsOfUnity <| χ.apply_mem_rootsOfUnity a).symm
lemma star_apply' (χ : MulChar R ℂ) (a : R) : star (χ a) = χ⁻¹ a := by
  simp only [RCLike.star_def, ← star_eq_inv, star_apply]
end Ring
section IsCyclic
variable {M : Type*} [CommMonoid M] [Fintype M] [DecidableEq M]
variable {R : Type*} [CommMonoidWithZero R]
noncomputable def ofRootOfUnity {ζ : Rˣ} (hζ : ζ ∈ rootsOfUnity (Fintype.card Mˣ) R)
    {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    MulChar M R := by
  have : orderOf ζ ∣ Fintype.card Mˣ :=
    orderOf_dvd_iff_pow_eq_one.mpr <| (mem_rootsOfUnity _ ζ).mp hζ
  refine ofUnitHom <| monoidHomOfForallMemZpowers hg <| this.trans <| dvd_of_eq ?_
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
lemma ofRootOfUnity_spec {ζ : Rˣ} (hζ : ζ ∈ rootsOfUnity (Fintype.card Mˣ) R)
    {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ofRootOfUnity hζ hg g = ζ := by
  simp only [ofRootOfUnity, ofUnitHom_eq, equivToUnitHom_symm_coe,
    monoidHomOfForallMemZpowers_apply_gen]
variable (M R) in
noncomputable def equiv_rootsOfUnity [inst_cyc : IsCyclic Mˣ] :
    MulChar M R ≃* rootsOfUnity (Fintype.card Mˣ) R where
  toFun χ :=
    ⟨χ.toUnitHom <| Classical.choose inst_cyc.exists_generator, by
      simp only [toUnitHom_eq, mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]⟩
  invFun ζ := ofRootOfUnity ζ.prop <| Classical.choose_spec inst_cyc.exists_generator
  left_inv χ := by
    simp only [toUnitHom_eq, eq_iff <| Classical.choose_spec inst_cyc.exists_generator,
      ofRootOfUnity_spec, coe_equivToUnitHom]
  right_inv ζ := by
    ext
    simp only [toUnitHom_eq, coe_equivToUnitHom, ofRootOfUnity_spec]
  map_mul' x y := by
    simp only [toUnitHom_eq, equivToUnitHom_mul_apply, MulMemClass.mk_mul_mk]
end IsCyclic
section FiniteField
section Fintype
variable (F : Type*) [Field F] [Fintype F]
variable {R : Type*} [CommRing R]
lemma exists_mulChar_orderOf {n : ℕ} (h : n ∣ Fintype.card F - 1) {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ χ : MulChar F R, orderOf χ = n := by
  classical
  have hn₀ : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn ↦ ?_
    simp only [hn, zero_dvd_iff, Nat.sub_eq_zero_iff_le] at h
    exact (Fintype.one_lt_card.trans_le h).false
  let e := MulChar.equiv_rootsOfUnity F R
  let ζ' : Rˣ := (hζ.isUnit hn₀).unit
  have h' : ζ' ^ (Fintype.card Fˣ : ℕ) = 1 :=
    Units.ext_iff.mpr <| (hζ.pow_eq_one_iff_dvd _).mpr <| Fintype.card_units (α := F) ▸ h
  use e.symm ⟨ζ', (mem_rootsOfUnity (Fintype.card Fˣ) ζ').mpr h'⟩
  rw [e.symm.orderOf_eq, orderOf_eq_iff hn₀]
  refine ⟨?_, fun m hm hm₀ h ↦ ?_⟩
  · ext
    push_cast
    exact hζ.pow_eq_one
  · rw [Subtype.ext_iff, Units.ext_iff] at h
    push_cast at h
    exact ((Nat.le_of_dvd hm₀ <| hζ.dvd_of_pow_eq_one _ h).trans_lt hm).false
lemma orderOf_dvd_card_sub_one (χ : MulChar F R) : orderOf χ ∣ Fintype.card F - 1 := by
  classical
  rw [← Fintype.card_units]
  exact orderOf_dvd_of_pow_eq_one χ.pow_card_eq_one
lemma exists_mulChar_orderOf_eq_card_units [DecidableEq F]
    {ζ : R} (hζ : IsPrimitiveRoot ζ (Fintype.card Fˣ)) :
    ∃ χ : MulChar F R, orderOf χ = Fintype.card Fˣ :=
  exists_mulChar_orderOf F (by rw [Fintype.card_units]) hζ
end Fintype
variable {F : Type*} [Field F] [Finite F]
variable {R : Type*} [CommRing R]
lemma apply_mem_rootsOfUnity_orderOf (χ : MulChar F R) {a : F} (ha : a ≠ 0) :
    ∃ ζ ∈ rootsOfUnity (orderOf χ) R, ζ = χ a := by
  have hu : IsUnit (χ a) := ha.isUnit.map χ
  refine ⟨hu.unit, ?_, hu.unit_spec⟩
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
    IsUnit.unit_spec, ← χ.pow_apply' χ.orderOf_pos.ne', pow_orderOf_eq_one,
    show a = (isUnit_iff_ne_zero.mpr ha).unit by simp only [IsUnit.unit_spec],
    MulChar.one_apply_coe]
lemma apply_mem_rootsOfUnity_of_pow_eq_one {χ : MulChar F R} {n : ℕ} (hχ : χ ^ n = 1)
    {a : F} (ha : a ≠ 0) :
    ∃ ζ ∈ rootsOfUnity n R, ζ = χ a := by
  obtain ⟨μ, hμ₁, hμ₂⟩ := χ.apply_mem_rootsOfUnity_orderOf ha
  exact ⟨μ, rootsOfUnity_le_of_dvd (orderOf_dvd_of_pow_eq_one hχ) hμ₁, hμ₂⟩
variable [IsDomain R]
lemma exists_apply_eq_pow {χ : MulChar F R} {n : ℕ} [NeZero n] (hχ : χ ^ n = 1) {μ : R}
    (hμ : IsPrimitiveRoot μ n) {a : F} (ha : a ≠ 0) :
    ∃ k < n, χ a = μ ^ k := by
  obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ ha
  have hζ' : ζ.val ^ n = 1 := (mem_rootsOfUnity' n ↑ζ).mp hζ₁
  obtain ⟨k, hk₁, hk₂⟩ := hμ.eq_pow_of_pow_eq_one hζ'
  exact ⟨k, hk₁, (hζ₂ ▸ hk₂).symm⟩
lemma apply_mem_algebraAdjoin_of_pow_eq_one {χ : MulChar F R} {n : ℕ} [NeZero n] (hχ : χ ^ n = 1)
    {μ : R} (hμ : IsPrimitiveRoot μ n) (a : F) :
    χ a ∈ Algebra.adjoin ℤ {μ} := by
  rcases eq_or_ne a 0 with rfl | h
  · exact χ.map_zero ▸ Subalgebra.zero_mem _
  · obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ h
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val] at hζ₁
    obtain ⟨k, _, hk⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hμ hζ₁
    exact hζ₂ ▸ hk ▸ Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) k
lemma apply_mem_algebraAdjoin {χ : MulChar F R} {μ : R} (hμ : IsPrimitiveRoot μ (orderOf χ))
    (a : F) :
    χ a ∈ Algebra.adjoin ℤ {μ} :=
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  apply_mem_algebraAdjoin_of_pow_eq_one (pow_orderOf_eq_one χ) hμ a
end FiniteField
end MulChar