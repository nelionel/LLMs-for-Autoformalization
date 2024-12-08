import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
open scoped nonZeroDivisors
open Localization Ideal IsLocalization
theorem IsIntegrallyClosed.of_localization_maximal {R : Type*} [CommRing R] [IsDomain R]
    (h : ∀ p : Ideal R, p ≠ ⊥ → [p.IsMaximal] → IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed R := by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  rintro ⟨x⟩ hx
  let I : Ideal R := span {x.2.1} / span {x.1}
  have h1 : 1 ∈ I := by
    apply I.eq_top_iff_one.mp
    by_contra hn
    rcases I.exists_le_maximal hn with ⟨p, hpm, hpi⟩
    have hic := h p (Ring.ne_bot_of_isMaximal_of_not_isField hpm hf)
    have hxp : IsIntegral (Localization.AtPrime p) (mk x.1 x.2) := hx.tower_top
    rcases (isIntegrallyClosed_iff (FractionRing R)).mp hic hxp with ⟨⟨y⟩, hy⟩
    have hyi : y.2.1 ∈ I := by
      intro a ha
      rcases mem_span_singleton'.mp ha with ⟨b, hb⟩
      apply mem_span_singleton'.mpr ⟨b * y.1, _⟩
      rw [← hb, ← mul_assoc, mul_comm y.2.1 b, mul_assoc, mul_assoc]
      exact congrArg (HMul.hMul b) <| (mul_comm y.1 x.2.1).trans <|
        NoZeroSMulDivisors.algebraMap_injective R (Localization R⁰) <| mk'_eq_iff_eq.mp <|
          (mk'_eq_algebraMap_mk'_of_submonoid_le _ _ p.primeCompl_le_nonZeroDivisors y.1 y.2).trans
            <| show algebraMap (Localization.AtPrime p) _ (mk' _ y.1 y.2) = mk' _ x.1 x.2
              by simpa only [← mk_eq_mk', ← hy] using by rfl
    exact y.2.2 (hpi hyi)
  rcases mem_span_singleton'.mp (h1 x.1 (mem_span_singleton_self x.1)) with ⟨y, hy⟩
  exact ⟨y, (eq_mk'_of_mul_eq (hy.trans (one_mul x.1))).trans (mk_eq_mk'_apply x.1 x.2).symm⟩
theorem isIntegrallyClosed_ofLocalizationMaximal :
    OfLocalizationMaximal fun R _ => ([IsDomain R] → IsIntegrallyClosed R) :=
  fun _ _ h _ ↦ IsIntegrallyClosed.of_localization_maximal fun p _ hpm ↦ h p hpm