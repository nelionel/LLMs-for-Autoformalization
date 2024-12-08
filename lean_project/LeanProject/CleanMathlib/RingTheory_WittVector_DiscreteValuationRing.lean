import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.MulCoeff
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.LinearCombination
noncomputable section
namespace WittVector
variable {p : ℕ} [hp : Fact p.Prime]
local notation "𝕎" => WittVector p
section CommRing
variable {k : Type*} [CommRing k] [CharP k p]
def succNthValUnits (n : ℕ) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) → k) : k :=
  -↑(a⁻¹ ^ p ^ (n + 1)) *
    (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)
noncomputable def inverseCoeff (a : Units k) (A : 𝕎 k) : ℕ → k
  | 0 => ↑a⁻¹
  | n + 1 => succNthValUnits n a A fun i => inverseCoeff a A i.val
def mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k) :=
  Units.mkOfMulEqOne A (@WittVector.mk' p _ (inverseCoeff a A)) (by
    ext n
    induction' n with n _
    · simp [WittVector.mul_coeff_zero, inverseCoeff, hA]
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
      nthRemainder p n (truncateFun (n + 1) A) fun i : Fin (n + 1) => inverseCoeff a A i
    have H := Units.mul_inv (a ^ p ^ (n + 1))
    linear_combination (norm := skip) -H_coeff * H
    have ha : (a : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1)) := by norm_cast
    have ha_inv : (↑a⁻¹ : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1))⁻¹ := by norm_cast
    simp only [nthRemainder_spec, inverseCoeff, succNthValUnits, hA,
      one_coeff_eq_of_pos, Nat.succ_pos', ha_inv, ha, inv_pow]
    ring!)
@[simp]
theorem coe_mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mkUnit hA : 𝕎 k) = A :=
  rfl
end CommRing
section Field
variable {k : Type*} [Field k] [CharP k p]
theorem isUnit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 ≠ 0) : IsUnit x := by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  have hy : x.coeff 0 = y := rfl
  exact (mkUnit hy).isUnit
variable (p)
theorem irreducible : Irreducible (p : 𝕎 k) := by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [constantCoeff_apply, coeff_p_zero, not_isUnit_zero] using
      (constantCoeff : WittVector p k →+* _).isUnit_map hp
  refine ⟨hp, fun a b hab => ?_⟩
  obtain ⟨ha0, hb0⟩ : a ≠ 0 ∧ b ≠ 0 := by
    rw [← mul_ne_zero_iff]; intro h; rw [h] at hab; exact p_nonzero p k hab
  obtain ⟨m, a, ha, rfl⟩ := verschiebung_nonzero ha0
  obtain ⟨n, b, hb, rfl⟩ := verschiebung_nonzero hb0
  cases m; · exact Or.inl (isUnit_of_coeff_zero_ne_zero a ha)
  cases' n with n; · exact Or.inr (isUnit_of_coeff_zero_ne_zero b hb)
  rw [iterate_verschiebung_mul] at hab
  apply_fun fun x => coeff x 1 at hab
  simp only [coeff_p_one, Nat.add_succ, add_comm _ n, Function.iterate_succ', Function.comp_apply,
    verschiebung_coeff_add_one, verschiebung_coeff_zero] at hab
  exact (one_ne_zero hab).elim
end Field
section PerfectRing
variable {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
theorem exists_eq_pow_p_mul (a : 𝕎 k) (ha : a ≠ 0) :
    ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c
  rw [WittVector.iterate_frobenius_coeff] at hc
  have := congr_fun (WittVector.verschiebung_frobenius_comm.comp_iterate m) b
  simp only [Function.comp_apply] at this
  rw [← this] at hcm
  refine ⟨m, b, ?_, ?_⟩
  · contrapose! hc
    simp [hc, zero_pow <| pow_ne_zero _ hp.out.ne_zero]
  · simp_rw [← mul_left_iterate (p : 𝕎 k) m]
    convert hcm using 2
    ext1 x
    rw [mul_comm, ← WittVector.verschiebung_frobenius x]; rfl
end PerfectRing
section PerfectField
variable {k : Type*} [Field k] [CharP k p] [PerfectRing k p]
theorem exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a ≠ 0) :
    ∃ (m : ℕ) (b : Units (𝕎 k)), a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  let b₀ := Units.mk0 (b.coeff 0) h₁
  have hb₀ : b.coeff 0 = b₀ := rfl
  exact ⟨m, mkUnit hb₀, h₂⟩
theorem discreteValuationRing : DiscreteValuationRing (𝕎 k) :=
  DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization (by
    refine ⟨p, irreducible p, fun {x} hx => ?_⟩
    obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
    exact ⟨n, b, hb.symm⟩)
end PerfectField
end WittVector