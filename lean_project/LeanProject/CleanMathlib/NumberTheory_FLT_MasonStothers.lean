import Mathlib.RingTheory.Polynomial.Radical
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain
variable {k : Type*} [Field k] [DecidableEq k]
private theorem abc_subcall {a b c w : k[X]} {hw : w ≠ 0} (wab : w = wronskian a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (abc_dr_dvd_w : divRadical (a * b * c) ∣ w) :
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  have ab_nz := mul_ne_zero ha hb
  have abc_nz := mul_ne_zero ab_nz hc
  set abc_dr := divRadical (a * b * c)
  have abc_dr_ndeg_lt : abc_dr.natDegree < a.natDegree + b.natDegree := by
    calc
      abc_dr.natDegree ≤ w.natDegree := Polynomial.natDegree_le_of_dvd abc_dr_dvd_w hw
      _ < a.natDegree + b.natDegree := by rw [wab] at hw ⊢; exact natDegree_wronskian_lt_add hw
  set abc_r := radical (a * b * c)
  apply Nat.lt_of_add_lt_add_left
  calc
    a.natDegree + b.natDegree + c.natDegree = (a * b * c).natDegree := by
      rw [Polynomial.natDegree_mul ab_nz hc, Polynomial.natDegree_mul ha hb]
    _ = ((divRadical (a * b * c)) * (radical (a * b * c))).natDegree := by
      rw [mul_comm _ (radical _), radical_mul_divRadical (a * b * c)]
    _ = abc_dr.natDegree + abc_r.natDegree := by
      rw [← Polynomial.natDegree_mul (divRadical_ne_zero abc_nz) (radical_ne_zero (a * b * c))]
    _ < a.natDegree + b.natDegree + abc_r.natDegree := by
      exact Nat.add_lt_add_right abc_dr_ndeg_lt _
theorem Polynomial.abc {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (hbc : IsCoprime b c) (hca : IsCoprime c a) (hsum : a + b + c = 0) :
    ( natDegree a + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree b + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree c + 1 ≤ (radical (a * b * c)).natDegree ) ∨
      derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  set w := wronskian a b with wab
  have wbc : w = wronskian b c := wronskian_eq_of_sum_zero hsum
  have wca : w = wronskian c a := by
    rw [add_rotate] at hsum
    simpa only [← wbc] using wronskian_eq_of_sum_zero hsum
  have abc_dr_dvd_w : divRadical (a * b * c) ∣ w := by
    have adr_dvd_w := divRadical_dvd_wronskian_left a b
    have bdr_dvd_w := divRadical_dvd_wronskian_right a b
    have cdr_dvd_w := divRadical_dvd_wronskian_right b c
    rw [← wab] at adr_dvd_w bdr_dvd_w
    rw [← wbc] at cdr_dvd_w
    rw [divRadical_mul (hca.symm.mul_left hbc), divRadical_mul hab]
    exact (hca.divRadical.symm.mul_left hbc.divRadical).mul_dvd
      (hab.divRadical.mul_dvd adr_dvd_w bdr_dvd_w) cdr_dvd_w
  by_cases hw : w = 0
  · right
    rw [hw] at wab wbc
    cases' hab.wronskian_eq_zero_iff.mp wab.symm with ga gb
    cases' hbc.wronskian_eq_zero_iff.mp wbc.symm with _ gc
    exact ⟨ga, gb, gc⟩
  · left
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wbc <;> assumption
    · rw [← mul_rotate] at abc_dr_dvd_w ⊢
      apply abc_subcall wca <;> assumption
    · apply abc_subcall wab <;> assumption