import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Algebra.Group.Units.Hom
open Valuation
variable {R A ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓA] [Algebra R A]
    (vR : Valuation R ΓR) (vA : Valuation A ΓA)
class IsValExtension : Prop where
  val_isEquiv_comap : vR.IsEquiv <| vA.comap (algebraMap R A)
namespace IsValExtension
section algebraMap
variable [IsValExtension vR vA]
theorem val_map_le_iff (x y : R) : vA (algebraMap R A x) ≤ vA (algebraMap R A y) ↔ vR x ≤ vR y :=
  val_isEquiv_comap.symm x y
theorem val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y := by
  simpa only [not_le] using ((val_map_le_iff vR vA _ _).not)
theorem val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  (IsEquiv.val_eq val_isEquiv_comap).symm
theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1 := by
  simpa only [_root_.map_one] using val_map_le_iff vR vA x 1
theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 := by
  simpa only [_root_.map_one, not_le] using (val_map_le_iff vR vA 1 x).not
theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 := by
  simpa only [le_antisymm_iff, _root_.map_one] using
    and_congr (val_map_le_iff vR vA x 1) (val_map_le_iff vR vA 1 x)
end algebraMap
instance id : IsValExtension vR vR where
  val_isEquiv_comap := by
    simp only [Algebra.id.map_eq_id, comap_id, IsEquiv.refl]
section integer
variable {K : Type*} [Field K] [Algebra K A] {ΓR ΓA ΓK: Type*}
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓA] {vR : Valuation R ΓR} {vK : Valuation K ΓK}
    {vA : Valuation A ΓA} [IsValExtension vR vA]
theorem ofComapInteger (h : vA.integer.comap (algebraMap K A) = vK.integer) :
    IsValExtension vK vA where
  val_isEquiv_comap := by
    rw [isEquiv_iff_val_le_one]
    intro x
    simp_rw [← Valuation.mem_integer_iff, ← h, Subring.mem_comap, mem_integer_iff, comap_apply]
instance instAlgebraInteger : Algebra vR.integer vA.integer where
  smul r a := ⟨r • a,
    Algebra.smul_def r (a : A) ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr r.2) a.2⟩
  __ := (algebraMap R A).restrict vR.integer vA.integer
    (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)
@[simp, norm_cast]
theorem val_smul (r : vR.integer) (a : vA.integer) : ↑(r • a : vA.integer) = (r : R) • (a : A) := by
  rfl
@[simp, norm_cast]
theorem val_algebraMap (r : vR.integer) :
    ((algebraMap vR.integer vA.integer) r : A) = (algebraMap R A) (r : R) := by
  rfl
instance instIsScalarTowerInteger : IsScalarTower vR.integer vA.integer A where
  smul_assoc x y z := by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _
instance instNoZeroSMulDivisorsInteger [NoZeroSMulDivisors R A] :
    NoZeroSMulDivisors vR.integer vA.integer := by
  refine ⟨fun {x y} e ↦ ?_⟩
  have : (x : R) • (y : A) = 0 := by simpa [Subtype.ext_iff, Algebra.smul_def] using e
  simpa only [Subtype.ext_iff, smul_eq_zero] using this
theorem algebraMap_injective [IsValExtension vK vA] [Nontrivial A] :
    Function.Injective (algebraMap vK.integer vA.integer) := by
  intro x y h
  simp only [Subtype.ext_iff, val_algebraMap] at h
  ext
  apply RingHom.injective (algebraMap K A) h
@[instance]
theorem instIsLocalHomValuationInteger {S ΓS: Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero ΓS]
    [Algebra R S] [IsLocalHom (algebraMap R S)] {vS : Valuation S ΓS}
    [IsValExtension vR vS] : IsLocalHom (algebraMap vR.integer vS.integer) where
  map_nonunit r hr := by
    apply (Valuation.integer.integers (v := vR)).isUnit_of_one
    · exact (isUnit_map_iff (algebraMap R S) _).mp (hr.map (algebraMap _ S))
    · apply (Valuation.integer.integers (v := vS)).one_of_isUnit at hr
      exact (val_map_eq_one_iff vR vS _).mp hr
@[deprecated (since := "2024-10-10")]
alias instIsLocalRingHomValuationInteger := instIsLocalHomValuationInteger
end integer
end IsValExtension