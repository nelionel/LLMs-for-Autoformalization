import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.MonoidLocalization.Cardinality
import Mathlib.RingTheory.OreLocalization.Cardinality
open Cardinal nonZeroDivisors
universe u v
section CommSemiring
variable {R : Type u} [CommSemiring R] {L : Type v} [CommSemiring L] [Algebra R L]
namespace IsLocalization
theorem lift_cardinalMk_le (S : Submonoid R) [IsLocalization S L] :
    Cardinal.lift.{u} #L ≤ Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk_le S
  rwa [← lift_le.{v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this
theorem cardinalMk_le {L : Type u} [CommSemiring L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] : #L ≤ #R := by
  simpa using lift_cardinalMk_le (L := L) S
@[deprecated (since := "2024-10-30")] alias card_le := cardinalMk_le
end IsLocalization
end CommSemiring
section CommRing
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
namespace Localization
theorem cardinalMk {S : Submonoid R} (hS : S ≤ R⁰) : #(Localization S) = #R := by
  apply OreLocalization.cardinalMk
  convert hS using 1
  ext x
  rw [mem_nonZeroDivisorsRight_iff, mem_nonZeroDivisors_iff]
  congr! 3
  rw [mul_comm]
end Localization
namespace IsLocalization
variable (L)
theorem lift_cardinalMk (S : Submonoid R) [IsLocalization S L] (hS : S ≤ R⁰) :
    Cardinal.lift.{u} #L = Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk hS
  rwa [← lift_inj.{u, v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this
theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] (hS : S ≤ R⁰) : #L = #R := by
  simpa using lift_cardinalMk L S hS
@[deprecated (since := "2024-10-30")] alias card := cardinalMk
end IsLocalization
@[simp]
theorem Cardinal.mk_fractionRing (R : Type u) [CommRing R] : #(FractionRing R) = #R :=
  IsLocalization.cardinalMk (FractionRing R) R⁰ le_rfl
alias FractionRing.cardinalMk := Cardinal.mk_fractionRing
namespace IsFractionRing
variable (R L)
theorem lift_cardinalMk [IsFractionRing R L] : Cardinal.lift.{u} #L = Cardinal.lift.{v} #R :=
  IsLocalization.lift_cardinalMk L _ le_rfl
theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L] [IsFractionRing R L] : #L = #R :=
  IsLocalization.cardinalMk L _ le_rfl
end IsFractionRing
end CommRing