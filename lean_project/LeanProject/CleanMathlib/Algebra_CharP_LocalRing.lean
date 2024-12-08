import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
theorem charP_zero_or_prime_power (R : Type*) [CommRing R] [IsLocalRing R] (q : ℕ)
    [char_R_q : CharP R q] : q = 0 ∨ IsPrimePow q := by
  apply or_iff_not_imp_left.2
  intro q_pos
  let K := IsLocalRing.ResidueField R
  haveI RM_char := ringChar.charP K
  let r := ringChar K
  let n := q.factorization r
  rcases CharP.char_is_prime_or_zero K r with r_prime | r_zero
  · let a := q / r ^ n
    have q_eq_a_mul_rn : q = r ^ n * a := by rw [Nat.mul_div_cancel' (Nat.ordProj_dvd q r)]
    have r_ne_dvd_a := Nat.not_dvd_ordCompl r_prime q_pos
    have rn_dvd_q : r ^ n ∣ q := ⟨a, q_eq_a_mul_rn⟩
    rw [mul_comm] at q_eq_a_mul_rn
    have a_unit : IsUnit (a : R) := by
      by_contra g
      rw [← mem_nonunits_iff] at g
      rw [← IsLocalRing.mem_maximalIdeal] at g
      have a_cast_zero := Ideal.Quotient.eq_zero_iff_mem.2 g
      rw [map_natCast] at a_cast_zero
      have r_dvd_a := (ringChar.spec K a).1 a_cast_zero
      exact absurd r_dvd_a r_ne_dvd_a
    have rn_cast_zero : ↑(r ^ n) = (0 : R) := by
      rw [← @mul_one R _ ↑(r ^ n), mul_comm, ← Classical.choose_spec a_unit.exists_left_inv,
        mul_assoc, ← Nat.cast_mul, ← q_eq_a_mul_rn, CharP.cast_eq_zero R q]
      simp
    have q_eq_rn := Nat.dvd_antisymm ((CharP.cast_eq_zero_iff R q (r ^ n)).mp rn_cast_zero) rn_dvd_q
    have n_pos : n ≠ 0 := fun n_zero =>
      absurd (by simpa [n_zero] using q_eq_rn) (CharP.char_ne_one R q)
    exact ⟨r, ⟨n, ⟨r_prime.prime, ⟨pos_iff_ne_zero.mpr n_pos, q_eq_rn.symm⟩⟩⟩⟩
  · haveI K_char_p_0 := ringChar.of_eq r_zero
    haveI K_char_zero : CharZero K := CharP.charP_to_charZero K
    haveI R_char_zero := RingHom.charZero (IsLocalRing.residue R)
    have q_zero := CharP.eq R char_R_q (CharP.ofCharZero R)
    exact absurd q_zero q_pos