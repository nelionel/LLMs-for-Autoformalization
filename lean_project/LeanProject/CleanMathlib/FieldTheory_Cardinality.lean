import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Rat.Encodable
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.SetTheory.Cardinal.Divisibility
local notation "‖" x "‖" => Fintype.card x
open scoped Cardinal nonZeroDivisors
universe u
theorem Fintype.isPrimePow_card_of_field {α} [Fintype α] [Field α] : IsPrimePow ‖α‖ := by
  cases' CharP.exists α with p _
  haveI hp := Fact.mk (CharP.char_is_prime α p)
  letI : Algebra (ZMod p) α := ZMod.algebra _ _
  let b := IsNoetherian.finsetBasis (ZMod p) α
  rw [Module.card_fintype b, ZMod.card, isPrimePow_pow_iff]
  · exact hp.1.isPrimePow
  rw [← Module.finrank_eq_card_basis b]
  exact Module.finrank_pos.ne'
theorem Fintype.nonempty_field_iff {α} [Fintype α] : Nonempty (Field α) ↔ IsPrimePow ‖α‖ := by
  refine ⟨fun ⟨h⟩ => Fintype.isPrimePow_card_of_field, ?_⟩
  rintro ⟨p, n, hp, hn, hα⟩
  haveI := Fact.mk hp.nat_prime
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  exact ⟨(Fintype.equivOfCardEq
    (((Fintype.card_eq_nat_card).trans (GaloisField.card p n hn.ne')).trans hα)).symm.field⟩
theorem Fintype.not_isField_of_card_not_prime_pow {α} [Fintype α] [Ring α] :
    ¬IsPrimePow ‖α‖ → ¬IsField α :=
  mt fun h => Fintype.nonempty_field_iff.mp ⟨h.toField⟩
theorem Infinite.nonempty_field {α : Type u} [Infinite α] : Nonempty (Field α) := by
  suffices #α = #(FractionRing (MvPolynomial α <| ULift.{u} ℚ)) from
    (Cardinal.eq.1 this).map (·.field)
  simp
theorem Field.nonempty_iff {α : Type u} : Nonempty (Field α) ↔ IsPrimePow #α := by
  rw [Cardinal.isPrimePow_iff]
  cases' fintypeOrInfinite α with h h
  · simpa only [Cardinal.mk_fintype, Nat.cast_inj, exists_eq_left',
      (Cardinal.nat_lt_aleph0 _).not_le, false_or] using Fintype.nonempty_field_iff
  · simpa only [← Cardinal.infinite_iff, h, true_or, iff_true] using Infinite.nonempty_field