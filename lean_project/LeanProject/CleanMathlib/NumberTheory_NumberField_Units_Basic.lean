import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.LocalRing.RingHom.Basic
open scoped NumberField
noncomputable section
open NumberField Units
section Rat
theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl
end Rat
variable (K : Type*) [Field K]
section IsUnit
variable {K}
theorem NumberField.isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]
end IsUnit
namespace NumberField.Units
section coe
instance : CoeHTC (𝓞 K)ˣ K :=
  ⟨fun x => algebraMap _ K (Units.val x)⟩
theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  RingOfIntegers.coe_injective.comp Units.ext
variable {K}
theorem coe_coe (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) = (u : K) := rfl
theorem coe_mul (x y : (𝓞 K)ˣ) : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K) := rfl
theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n := by
  rw [← map_pow, ← val_pow_eq_pow_val]
theorem coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : (↑(x ^ n) : K) = (x : K) ^ n := by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n
theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl
theorem coe_neg_one : ((-1 : (𝓞 K)ˣ) : K) = (-1 : K) := rfl
theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)
end coe
open NumberField.InfinitePlace
@[simp]
protected theorem norm [NumberField K] (x : (𝓞 K)ˣ) :
    |Algebra.norm ℚ (x : K)| = 1 := by
  rw [← RingOfIntegers.coe_norm, isUnit_iff_norm.mp x.isUnit]
section torsion
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ
theorem mem_torsion {x : (𝓞 K)ˣ} [NumberField K] :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion]
  refine ⟨fun hx φ ↦ (((φ.comp <| algebraMap (𝓞 K) K).toMonoidHom.comp <|
    Units.coeHom _).isOfFinOrder hx).norm_eq_one, fun h ↦ isOfFinOrder_iff_pow_eq_one.2 ?_⟩
  obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.isIntegral_coe h
  exact ⟨n, hn, by ext; rw [NumberField.RingOfIntegers.coe_eq_algebraMap, coe_pow, hx,
    NumberField.RingOfIntegers.coe_eq_algebraMap, coe_one]⟩
instance [NumberField K] : Fintype (torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)
instance : Nonempty (torsion K) := One.instNonempty
instance [NumberField K] : IsCyclic (torsion K) := subgroup_units_cyclic _
def torsionOrder [NumberField K] : ℕ+ := ⟨Fintype.card (torsion K), Fintype.card_pos⟩
theorem rootsOfUnity_eq_one [NumberField K] {k : ℕ+} (hc : Nat.Coprime k (torsionOrder K))
    {ζ : (𝓞 K)ˣ} : ζ ∈ rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ, hζ⟩ : torsion K)]
    exact orderOf_dvd_card
theorem rootsOfUnity_eq_torsion [NumberField K] :
    rootsOfUnity (torsionOrder K) (𝓞 K) = torsion K := by
  ext ζ
  rw [torsion, mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨↑(torsionOrder K), (torsionOrder K).prop, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one (torsion K) _ _ ⟨ζ, h⟩)
end torsion
end Units
end NumberField