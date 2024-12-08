import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
open Function Valuation
open scoped Multiplicative
variable {K : Type*} [Field K] (v : Valuation K ℤₘ₀) (L : Type*) [Field L] [Algebra K L]
namespace ValuationSubring
instance : Algebra v.valuationSubring L := Algebra.ofSubring v.valuationSubring.toSubring
theorem algebraMap_injective : Injective (algebraMap v.valuationSubring L) :=
  (NoZeroSMulDivisors.algebraMap_injective K L).comp (IsFractionRing.injective _ _)
theorem isIntegral_of_mem_ringOfIntegers {x : L} (hx : x ∈ integralClosure v.valuationSubring L) :
    IsIntegral v.valuationSubring (⟨x, hx⟩ : integralClosure v.valuationSubring L) := by
  obtain ⟨P, hPm, hP⟩ := hx
  refine ⟨P, hPm, ?_⟩
  rw [← Polynomial.aeval_def, ← Subalgebra.coe_eq_zero, Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_def, Subtype.coe_mk, hP]
theorem isIntegral_of_mem_ringOfIntegers' {x : (integralClosure v.valuationSubring L)} :
    IsIntegral v.valuationSubring (x : integralClosure v.valuationSubring L) := by
  apply isIntegral_of_mem_ringOfIntegers
variable (E : Type _) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
instance : IsScalarTower v.valuationSubring L E := Subring.instIsScalarTowerSubtypeMem _
instance algebra :
    Algebra (integralClosure v.valuationSubring L) (integralClosure v.valuationSubring E) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap L E k, IsIntegral.algebraMap k.2⟩
      map_zero' :=
        Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_zero, _root_.map_zero]
      map_one' := Subtype.ext <| by simp only [Subtype.coe_mk, Subalgebra.coe_one, _root_.map_one]
      map_add' := fun x y =>
        Subtype.ext <| by simp only [_root_.map_add, Subalgebra.coe_add, Subtype.coe_mk]
      map_mul' := fun x y =>
        Subtype.ext <| by simp only [Subalgebra.coe_mul, _root_.map_mul, Subtype.coe_mk] }
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra v.valuationSubring R]
    [Algebra R L] [IsScalarTower v.valuationSubring R L]
    [IsIntegralClosure R v.valuationSubring L] : integralClosure v.valuationSubring L ≃+* R := by
  have := IsScalarTower.subalgebra' (valuationSubring v) L L
    (integralClosure (valuationSubring v) L)
  exact (IsIntegralClosure.equiv v.valuationSubring R L
    (integralClosure v.valuationSubring L)).symm.toRingEquiv
theorem integralClosure_algebraMap_injective :
    Injective (algebraMap v.valuationSubring (integralClosure v.valuationSubring L)) := by
  have hinj : Injective ⇑(algebraMap v.valuationSubring L) :=
    ValuationSubring.algebraMap_injective v L
  rw [injective_iff_map_eq_zero (algebraMap v.valuationSubring _)]
  intro x hx
  rw [← Subtype.coe_inj, Subalgebra.coe_zero] at hx
  rw [injective_iff_map_eq_zero (algebraMap v.valuationSubring L)] at hinj
  exact hinj x hx
end ValuationSubring