import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.ZMod.Quotient
import Mathlib.RingTheory.DedekindDomain.AdicValuation
set_option quotPrecheck false
local notation K "/" n => Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range
namespace IsDedekindDomain
noncomputable section
open scoped Multiplicative nonZeroDivisors
universe u v
variable {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace HeightOneSpectrum
open Classical in
def valuationOfNeZeroToFun (x : Kˣ) : Multiplicative ℤ :=
  let hx := IsLocalization.sec R⁰ (x : K)
  Multiplicative.ofAdd <|
    (-(Associates.mk v.asIdeal).count (Associates.mk <| Ideal.span {hx.fst}).factors : ℤ) -
      (-(Associates.mk v.asIdeal).count (Associates.mk <| Ideal.span {(hx.snd : R)}).factors : ℤ)
@[simp]
theorem valuationOfNeZeroToFun_eq (x : Kˣ) :
    (v.valuationOfNeZeroToFun x : ℤₘ₀) = v.valuation (x : K) := by
  classical
  rw [show v.valuation (x : K) = _ * _ by rfl]
  rw [Units.val_inv_eq_inv_val]
  change _ = ite _ _ _ * (ite _ _ _)⁻¹
  simp_rw [IsLocalization.toLocalizationMap_sec, SubmonoidClass.coe_subtype,
    if_neg <| IsLocalization.sec_fst_ne_zero le_rfl x.ne_zero,
    if_neg (nonZeroDivisors.coe_ne_zero _),
    valuationOfNeZeroToFun, ofAdd_sub, ofAdd_neg, div_inv_eq_mul, WithZero.coe_mul,
    WithZero.coe_inv, inv_inv]
def valuationOfNeZero : Kˣ →* Multiplicative ℤ where
  toFun := v.valuationOfNeZeroToFun
  map_one' := by rw [← WithZero.coe_inj, valuationOfNeZeroToFun_eq]; exact map_one _
  map_mul' _ _ := by
    rw [← WithZero.coe_inj, WithZero.coe_mul]
    simp only [valuationOfNeZeroToFun_eq]; exact map_mul _ _ _
@[simp]
theorem valuationOfNeZero_eq (x : Kˣ) : (v.valuationOfNeZero x : ℤₘ₀) = v.valuation (x : K) :=
  valuationOfNeZeroToFun_eq v x
@[simp]
theorem valuation_of_unit_eq (x : Rˣ) :
    v.valuationOfNeZero (Units.map (algebraMap R K : R →* K) x) = 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, Units.coe_map, eq_iff_le_not_lt]
  constructor
  · exact v.valuation_le_one x
  · cases' x with x _ hx _
    change ¬v.valuation (algebraMap R K x) < 1
    apply_fun v.intValuation at hx
    rw [map_one, map_mul] at hx
    rw [not_lt, ← hx, ← mul_one <| v.valuation _, valuation_of_algebraMap,
      mul_le_mul_left <| zero_lt_iff.2 <| left_ne_zero_of_mul_eq_one hx]
    exact v.intValuation_le_one _
def valuationOfNeZeroMod (n : ℕ) : (K/n) →* Multiplicative (ZMod n) :=
  (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.toMonoidHom.comp <|
    QuotientGroup.map (powMonoidHom n : Kˣ →* Kˣ).range
      (AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)))
      v.valuationOfNeZero
      (by
        rintro _ ⟨x, rfl⟩
        exact
          ⟨v.valuationOfNeZero x, by simp only [powMonoidHom_apply, map_pow, Int.toAdd_pow]; rfl⟩)
@[simp]
theorem valuation_of_unit_mod_eq (n : ℕ) (x : Rˣ) :
    v.valuationOfNeZeroMod n (Units.map (algebraMap R K : R →* K) x : K/n) = 1 := by
  erw [valuationOfNeZeroMod, MonoidHom.comp_apply, ← QuotientGroup.coe_mk',
    QuotientGroup.map_mk' (G := Kˣ) (N := MonoidHom.range (powMonoidHom n)),
    valuation_of_unit_eq, QuotientGroup.mk_one, map_one]
end HeightOneSpectrum
variable {S S' : Set <| HeightOneSpectrum R} {n : ℕ}
def selmerGroup : Subgroup <| K/n where
  carrier := {x : K/n | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuationOfNeZeroMod n x = 1}
  one_mem' _ _ := by rw [map_one]
  mul_mem' hx hy v hv := by rw [map_mul, hx v hv, hy v hv, one_mul]
  inv_mem' hx v hv := by rw [map_inv, hx v hv, inv_one]
local notation K "⟮" S "," n "⟯" => @selmerGroup _ _ _ K _ _ _ S n
namespace selmerGroup
theorem monotone (hS : S ≤ S') : K⟮S,n⟯ ≤ K⟮S',n⟯ := fun _ hx v => hx v ∘ mt (@hS v)
def valuation : K⟮S,n⟯ →* S → Multiplicative (ZMod n) where
  toFun x v := (v : HeightOneSpectrum R).valuationOfNeZeroMod n (x : K/n)
  map_one' := funext fun _ => map_one _
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul]; rfl
theorem valuation_ker_eq :
    valuation.ker = K⟮(∅ : Set <| HeightOneSpectrum R),n⟯.subgroupOf (K⟮S,n⟯) := by
  ext ⟨_, hx⟩
  constructor
  · intro hx' v _
    by_cases hv : v ∈ S
    · exact congr_fun hx' ⟨v, hv⟩
    · exact hx v hv
  · exact fun hx' => funext fun v => hx' v <| Set.not_mem_empty v
def fromUnit {n : ℕ} : Rˣ →* K⟮(∅ : Set <| HeightOneSpectrum R),n⟯ where
  toFun x :=
    ⟨QuotientGroup.mk <| Units.map (algebraMap R K).toMonoidHom x, fun v _ =>
      v.valuation_of_unit_mod_eq n x⟩
  map_one' := by simp only [map_one, QuotientGroup.mk_one, Subgroup.mk_eq_one]
  map_mul' _ _ := by simp only [RingHom.toMonoidHom_eq_coe, map_mul, QuotientGroup.mk_mul,
    MulMemClass.mk_mul_mk]
theorem fromUnit_ker [hn : Fact <| 0 < n] :
    (@fromUnit R _ _ K _ _ _ n).ker = (powMonoidHom n : Rˣ →* Rˣ).range := by
  ext ⟨_, _, _, _⟩
  constructor
  · intro hx
    rcases (QuotientGroup.eq_one_iff _).mp (Subtype.mk.inj hx) with ⟨⟨v, i, vi, iv⟩, hx⟩
    have hv : ↑(_ ^ n : Kˣ) = algebraMap R K _ := congr_arg Units.val hx
    have hi : ↑(_ ^ n : Kˣ)⁻¹ = algebraMap R K _ := congr_arg Units.inv hx
    rw [Units.val_pow_eq_pow_val] at hv
    rw [← inv_pow, Units.inv_mk, Units.val_pow_eq_pow_val] at hi
    rcases IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (x := v) hn.out
        (hv.symm ▸ isIntegral_algebraMap) with
      ⟨v', rfl⟩
    rcases IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (x := i) hn.out
        (hi.symm ▸ isIntegral_algebraMap) with
      ⟨i', rfl⟩
    rw [← map_mul, map_eq_one_iff _ <| NoZeroSMulDivisors.algebraMap_injective R K] at vi
    rw [← map_mul, map_eq_one_iff _ <| NoZeroSMulDivisors.algebraMap_injective R K] at iv
    rw [Units.val_mk, ← map_pow] at hv
    exact ⟨⟨v', i', vi, iv⟩, by
      simpa only [Units.ext_iff, powMonoidHom_apply, Units.val_pow_eq_pow_val] using
         NoZeroSMulDivisors.algebraMap_injective R K hv⟩
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact Subtype.mk_eq_mk.mpr <| (QuotientGroup.eq_one_iff _).mpr ⟨Units.map (algebraMap R K) x,
      by simp only [powMonoidHom_apply, RingHom.toMonoidHom_eq_coe, map_pow]⟩
def fromUnitLift [Fact <| 0 < n] : (R/n) →* K⟮(∅ : Set <| HeightOneSpectrum R),n⟯ :=
  (QuotientGroup.kerLift _).comp
    (QuotientGroup.quotientMulEquivOfEq (fromUnit_ker (R := R))).symm.toMonoidHom
theorem fromUnitLift_injective [Fact <| 0 < n] :
    Function.Injective <| @fromUnitLift R _ _ K _ _ _ n _ := by
  dsimp only [fromUnitLift, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact Function.Injective.comp (QuotientGroup.kerLift_injective _) (MulEquiv.injective _)
end selmerGroup
end
end IsDedekindDomain