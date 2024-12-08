import Mathlib.RingTheory.DedekindDomain.AdicValuation
namespace Set
noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors
universe u v
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
@[simps!]
def integer : Subalgebra R K :=
  {
    (⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.toSubring).copy
        {x : K | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation x ≤ 1} <|
      Set.ext fun _ => by simp [SetLike.mem_coe, Subring.mem_iInf] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }
theorem integer_eq :
    (S.integer K).toSubring =
      ⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.toSubring :=
  SetLike.ext' <| by ext; simp
theorem integer_valuation_le_one (x : S.integer K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation (x : K) ≤ 1 :=
  x.property v hv
@[simps!]
def unit : Subgroup Kˣ :=
  (⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.unitGroup).copy
      {x : Kˣ | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation (x : K) = 1} <|
    Set.ext fun _ => by
      simp only [mem_setOf, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]
theorem unit_eq :
    S.unit K = ⨅ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation.valuationSubring.unitGroup :=
  Subgroup.copy_eq _ _ _
theorem unit_valuation_eq_one (x : S.unit K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation ((x : Kˣ) : K) = 1 :=
  x.property v hv
@[simps apply_val_coe symm_apply_coe]
def unitEquivUnitsInteger : S.unit K ≃* (S.integer K)ˣ where
  toFun x :=
    ⟨⟨((x : Kˣ) : K), fun v hv => (x.property v hv).le⟩,
      ⟨((x⁻¹ : Kˣ) : K), fun v hv => (x⁻¹.property v hv).le⟩,
      Subtype.ext x.val.val_inv, Subtype.ext x.val.inv_val⟩
  invFun x :=
    ⟨Units.mk0 x fun hx => x.ne_zero (ZeroMemClass.coe_eq_zero.mp hx),
    fun v hv =>
      eq_one_of_one_le_mul_left (x.val.property v hv) (x.inv.property v hv) <|
        Eq.ge <| by
          rw [Units.val_mk0, ← map_mul, Subtype.mk_eq_mk.mp x.val_inv, v.valuation.map_one]⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
end
end Set