import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Nat.Factors
universe u
open Nat
open multiplicity
variable {p : ℕ}
def padicValNat (p : ℕ) (n : ℕ) : ℕ :=
  if h : p ≠ 1 ∧ 0 < n then Nat.find (multiplicity_finite_iff.2 h) else 0
theorem padicValNat_def' {n : ℕ} (hp : p ≠ 1) (hn : 0 < n) :
    padicValNat p n = multiplicity p n := by
  simp [padicValNat, hp, hn, multiplicity, emultiplicity, multiplicity_finite_iff.2 ⟨hp, hn⟩]
  convert (WithTop.untop'_coe ..).symm
theorem padicValNat_def [hp : Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    padicValNat p n = multiplicity p n :=
  padicValNat_def' hp.out.ne_one hn
theorem padicValNat_eq_emultiplicity [hp : Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    padicValNat p n = emultiplicity p n := by
  rw [(multiplicity_finite_iff.2 ⟨hp.out.ne_one, hn⟩).emultiplicity_eq_multiplicity]
  exact_mod_cast padicValNat_def hn
namespace padicValNat
open multiplicity
open List
@[simp]
protected theorem zero : padicValNat p 0 = 0 := by simp [padicValNat]
@[simp]
protected theorem one : padicValNat p 1 = 0 := by simp [padicValNat]
@[simp]
theorem eq_zero_iff {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  simp only [padicValNat, ne_eq, pos_iff_ne_zero, dite_eq_right_iff, find_eq_zero, zero_add,
    pow_one, and_imp, ← or_iff_not_imp_left]
end padicValNat
open List
theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n a <+~ b.primeFactorsList :=
  (replicate_subperm_primeFactorsList_iff ha hb).trans
    pow_dvd_iff_le_emultiplicity |>.symm
@[deprecated (since := "2024-07-17")]
alias le_multiplicity_iff_replicate_subperm_factors :=
  le_emultiplicity_iff_replicate_subperm_primeFactorsList
theorem le_padicValNat_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    n ≤ padicValNat a b ↔ replicate n a <+~ b.primeFactorsList := by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb,
    Nat.multiplicity_finite_iff.2 ⟨ha.ne_one, Nat.pos_of_ne_zero hb⟩
      |>.emultiplicity_eq_multiplicity,     ← padicValNat_def' ha.ne_one (Nat.pos_of_ne_zero hb),
      Nat.cast_le]
@[deprecated (since := "2024-07-17")]
alias le_padicValNat_iff_replicate_subperm_factors :=
  le_padicValNat_iff_replicate_subperm_primeFactorsList