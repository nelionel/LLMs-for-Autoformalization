import Mathlib.Algebra.CharP.LocalRing
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.FieldSimp
variable (R : Type*) [CommRing R]
class MixedCharZero (p : ℕ) : Prop where
  [toCharZero : CharZero R]
  charP_quotient : ∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p
namespace MixedCharZero
theorem reduce_to_p_prime {P : Prop} :
    (∀ p > 0, MixedCharZero R p → P) ↔ ∀ p : ℕ, p.Prime → MixedCharZero R p → P := by
  constructor
  · intro h q q_prime q_mixedChar
    exact h q (Nat.Prime.pos q_prime) q_mixedChar
  · intro h q q_pos q_mixedChar
    rcases q_mixedChar.charP_quotient with ⟨I, hI_ne_top, _⟩
    rcases Ideal.exists_le_maximal I hI_ne_top with ⟨M, hM_max, h_IM⟩
    let r := ringChar (R ⧸ M)
    have r_pos : r ≠ 0 := by
      have q_zero :=
        congr_arg (Ideal.Quotient.factor I M h_IM) (CharP.cast_eq_zero (R ⧸ I) q)
      simp only [map_natCast, map_zero] at q_zero
      apply ne_zero_of_dvd_ne_zero (ne_of_gt q_pos)
      exact (CharP.cast_eq_zero_iff (R ⧸ M) r q).mp q_zero
    have r_prime : Nat.Prime r :=
      or_iff_not_imp_right.1 (CharP.char_is_prime_or_zero (R ⧸ M) r) r_pos
    apply h r r_prime
    have : CharZero R := q_mixedChar.toCharZero
    exact ⟨⟨M, hM_max.ne_top, ringChar.of_eq rfl⟩⟩
theorem reduce_to_maximal_ideal {p : ℕ} (hp : Nat.Prime p) :
    (∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p) ↔ ∃ I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
  constructor
  · intro g
    rcases g with ⟨I, ⟨hI_not_top, _⟩⟩
    rcases Ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM_ge⟩⟩
    use M
    constructor
    · exact hM_max
    · cases CharP.exists (R ⧸ M) with
      | intro r hr =>
        convert hr
        have r_dvd_p : r ∣ p := by
          rw [← CharP.cast_eq_zero_iff (R ⧸ M) r p]
          convert congr_arg (Ideal.Quotient.factor I M hM_ge) (CharP.cast_eq_zero (R ⧸ I) p)
        symm
        apply (Nat.Prime.eq_one_or_self_of_dvd hp r r_dvd_p).resolve_left
        exact CharP.char_ne_one (R ⧸ M) r
  · intro ⟨I, hI_max, h_charP⟩
    use I
    exact ⟨Ideal.IsMaximal.ne_top hI_max, h_charP⟩
end MixedCharZero
namespace EqualCharZero
theorem of_algebraRat [Algebra ℚ R] : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI
  constructor
  intro a b h_ab
  contrapose! hI
  refine I.eq_top_of_isUnit_mem ?_ (IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 (a - b : ℚ) ?_))
  · simpa only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_natCast]
  simpa only [Ne, sub_eq_zero] using (@Nat.cast_injective ℚ _ _).ne hI
section ConstructionAlgebraRat
variable {R}
theorem PNat.isUnit_natCast [h : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))]
    (n : ℕ+) : IsUnit (n : R) := by
  rw [← Ideal.span_singleton_eq_top]
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  intro h_char_zero
  apply h_char_zero.cast_injective.ne n.ne_zero
  rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)
@[coe]
noncomputable def pnatCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ℕ+ → Rˣ :=
  fun n => (PNat.isUnit_natCast n).unit
noncomputable instance coePNatUnits
    [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : Coe ℕ+ Rˣ :=
  ⟨EqualCharZero.pnatCast⟩
@[simp]
theorem pnatCast_one [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ((1 : ℕ+) : Rˣ) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  change ((PNat.isUnit_natCast (R := R) 1).unit : R) = 1
  rw [IsUnit.unit_spec (PNat.isUnit_natCast 1)]
  rw [PNat.one_coe, Nat.cast_one]
@[simp]
theorem pnatCast_eq_natCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] (n : ℕ+) :
    ((n : Rˣ) : R) = ↑n := by
  change ((PNat.isUnit_natCast (R := R) n).unit : R) = ↑n
  simp only [IsUnit.unit_spec]
noncomputable def algebraRat (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    Algebra ℚ R :=
  haveI : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
  { toFun := fun x => x.num /ₚ ↑x.pnatDen
    map_zero' := by simp [divp]
    map_one' := by simp
    map_mul' := by
      intro a b
      field_simp
      trans (↑((a * b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.mul_num_den' a b]
      simp
    map_add' := by
      intro a b
      field_simp
      trans (↑((a + b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.add_num_den' a b]
      simp }
end ConstructionAlgebraRat
theorem of_not_mixedCharZero [CharZero R] (h : ∀ p > 0, ¬MixedCharZero R p) :
    ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  intro I hI_ne_top
  suffices CharP (R ⧸ I) 0 from CharP.charP_to_charZero _
  cases CharP.exists (R ⧸ I) with
  | intro p hp =>
    cases p with
    | zero => exact hp
    | succ p =>
      have h_mixed : MixedCharZero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩
      exact absurd h_mixed (h p.succ p.succ_pos)
theorem to_not_mixedCharZero (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    ∀ p > 0, ¬MixedCharZero R p := by
  intro p p_pos
  by_contra hp_mixedChar
  rcases hp_mixedChar.charP_quotient with ⟨I, hI_ne_top, hI_p⟩
  replace hI_zero : CharP (R ⧸ I) 0 := @CharP.ofCharZero _ _ (h I hI_ne_top)
  exact absurd (CharP.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos)
theorem iff_not_mixedCharZero [CharZero R] :
    (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) ↔ ∀ p > 0, ¬MixedCharZero R p :=
  ⟨to_not_mixedCharZero R, of_not_mixedCharZero R⟩
theorem nonempty_algebraRat_iff :
    Nonempty (Algebra ℚ R) ↔ ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  constructor
  · intro h_alg
    haveI h_alg' : Algebra ℚ R := h_alg.some
    apply of_algebraRat
  · intro h
    apply Nonempty.intro
    exact algebraRat h
end EqualCharZero
theorem isEmpty_algebraRat_iff_mixedCharZero [CharZero R] :
    IsEmpty (Algebra ℚ R) ↔ ∃ p > 0, MixedCharZero R p := by
  rw [← not_iff_not]
  push_neg
  rw [not_isEmpty_iff, ← EqualCharZero.iff_not_mixedCharZero]
  apply EqualCharZero.nonempty_algebraRat_iff
section MainStatements
variable {P : Prop}
theorem split_equalCharZero_mixedCharZero [CharZero R] (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  by_cases h : ∃ p > 0, MixedCharZero R p
  · rcases h with ⟨p, ⟨H, hp⟩⟩
    rw [← MixedCharZero.reduce_to_p_prime] at h_mixed
    exact h_mixed p H hp
  · apply h_equal
    rw [← isEmpty_algebraRat_iff_mixedCharZero, not_isEmpty_iff] at h
    exact h.some
example (n : ℕ) (h : n ≠ 0) : 0 < n :=
  zero_lt_iff.mpr h
theorem split_by_characteristic (h_pos : ∀ p : ℕ, p ≠ 0 → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  cases CharP.exists R with
  | intro p p_charP =>
    by_cases h : p = 0
    · rw [h] at p_charP
      haveI h0 : CharZero R := CharP.charP_to_charZero R
      exact split_equalCharZero_mixedCharZero R h_equal h_mixed
    · exact h_pos p h p_charP
theorem split_by_characteristic_domain [IsDomain R] (h_pos : ∀ p : ℕ, Nat.Prime p → CharP R p → P)
    (h_equal : Algebra ℚ R → P) (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_prime : Nat.Prime p := or_iff_not_imp_right.mp (CharP.char_is_prime_or_zero R p) p_pos
  exact h_pos p p_prime p_char
theorem split_by_characteristic_localRing [IsLocalRing R]
    (h_pos : ∀ p : ℕ, IsPrimePow p → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  refine split_by_characteristic R ?_ h_equal h_mixed
  intro p p_pos p_char
  have p_ppow : IsPrimePow (p : ℕ) := or_iff_not_imp_left.mp (charP_zero_or_prime_power R p) p_pos
  exact h_pos p p_ppow p_char
end MainStatements