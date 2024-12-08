import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.Module.AEval
open Polynomial
namespace Polynomial
section Semiring
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable (R)
noncomputable def annIdeal (a : A) : Ideal R[X] :=
  RingHom.ker ((aeval a).toRingHom : R[X] →+* A)
variable {R}
theorem mem_annIdeal_iff_aeval_eq_zero {a : A} {p : R[X]} : p ∈ annIdeal R a ↔ aeval a p = 0 :=
  Iff.rfl
end Semiring
section Field
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
variable (𝕜)
open Submodule
noncomputable def annIdealGenerator (a : A) : 𝕜[X] :=
  let g := IsPrincipal.generator <| annIdeal 𝕜 a
  g * C g.leadingCoeff⁻¹
section
variable {𝕜}
@[simp]
theorem annIdealGenerator_eq_zero_iff {a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥ := by
  simp only [annIdealGenerator, mul_eq_zero, IsPrincipal.eq_bot_iff_generator_eq_zero,
    Polynomial.C_eq_zero, inv_eq_zero, Polynomial.leadingCoeff_eq_zero, or_self_iff]
end
@[simp]
theorem span_singleton_annIdealGenerator (a : A) :
    Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, annIdealGenerator_eq_zero_iff.mp h, Set.singleton_zero, Ideal.span_zero]
  · rw [annIdealGenerator, Ideal.span_singleton_mul_right_unit, Ideal.span_singleton_generator]
    apply Polynomial.isUnit_C.mpr
    apply IsUnit.mk0
    apply inv_eq_zero.not.mpr
    apply Polynomial.leadingCoeff_eq_zero.not.mpr
    apply (mul_ne_zero_iff.mp h).1
theorem annIdealGenerator_mem (a : A) : annIdealGenerator 𝕜 a ∈ annIdeal 𝕜 a :=
  Ideal.mul_mem_right _ _ (Submodule.IsPrincipal.generator_mem _)
theorem mem_iff_eq_smul_annIdealGenerator {p : 𝕜[X]} (a : A) :
    p ∈ annIdeal 𝕜 a ↔ ∃ s : 𝕜[X], p = s • annIdealGenerator 𝕜 a := by
  simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_annIdealGenerator 𝕜 a, Ideal.span]
theorem monic_annIdealGenerator (a : A) (hg : annIdealGenerator 𝕜 a ≠ 0) :
    Monic (annIdealGenerator 𝕜 a) :=
  monic_mul_leadingCoeff_inv (mul_ne_zero_iff.mp hg).1
theorem annIdealGenerator_aeval_eq_zero (a : A) : aeval a (annIdealGenerator 𝕜 a) = 0 :=
  mem_annIdeal_iff_aeval_eq_zero.mp (annIdealGenerator_mem 𝕜 a)
variable {𝕜}
theorem mem_iff_annIdealGenerator_dvd {p : 𝕜[X]} {a : A} :
    p ∈ annIdeal 𝕜 a ↔ annIdealGenerator 𝕜 a ∣ p := by
  rw [← Ideal.mem_span_singleton, span_singleton_annIdealGenerator]
theorem degree_annIdealGenerator_le_of_mem (a : A) (p : 𝕜[X]) (hp : p ∈ annIdeal 𝕜 a)
    (hpn0 : p ≠ 0) : degree (annIdealGenerator 𝕜 a) ≤ degree p :=
  degree_le_of_dvd (mem_iff_annIdealGenerator_dvd.1 hp) hpn0
variable (𝕜)
theorem annIdealGenerator_eq_minpoly (a : A) : annIdealGenerator 𝕜 a = minpoly 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, minpoly.eq_zero]
    rintro ⟨p, p_monic, hp : aeval a p = 0⟩
    refine p_monic.ne_zero (Ideal.mem_bot.mp ?_)
    simpa only [annIdealGenerator_eq_zero_iff.mp h] using mem_annIdeal_iff_aeval_eq_zero.mpr hp
  · exact minpoly.unique _ _ (monic_annIdealGenerator _ _ h) (annIdealGenerator_aeval_eq_zero _ _)
      fun q q_monic hq =>
        degree_annIdealGenerator_le_of_mem a q (mem_annIdeal_iff_aeval_eq_zero.mpr hq)
          q_monic.ne_zero
theorem monic_generator_eq_minpoly (a : A) (p : 𝕜[X]) (p_monic : p.Monic)
    (p_gen : Ideal.span {p} = annIdeal 𝕜 a) : annIdealGenerator 𝕜 a = p := by
  by_cases h : p = 0
  · rwa [h, annIdealGenerator_eq_zero_iff, ← p_gen, Ideal.span_singleton_eq_bot.mpr]
  · rw [← span_singleton_annIdealGenerator, Ideal.span_singleton_eq_span_singleton] at p_gen
    rw [eq_comm]
    apply eq_of_monic_of_associated p_monic _ p_gen
    apply monic_annIdealGenerator _ _ ((Associated.ne_zero_iff p_gen).mp h)
theorem span_minpoly_eq_annihilator {M} [AddCommGroup M] [Module 𝕜 M] (f : Module.End 𝕜 M) :
    Ideal.span {minpoly 𝕜 f} = Module.annihilator 𝕜[X] (Module.AEval' f) := by
  rw [← annIdealGenerator_eq_minpoly, span_singleton_annIdealGenerator]; ext
  rw [mem_annIdeal_iff_aeval_eq_zero, DFunLike.ext_iff, Module.mem_annihilator]; rfl
end Field
end Polynomial