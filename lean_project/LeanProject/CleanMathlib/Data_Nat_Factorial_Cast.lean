import Mathlib.RingTheory.Polynomial.Pochhammer
open Nat
variable (S : Type*)
namespace Nat
section Semiring
variable [Semiring S] (a b : ℕ)
theorem cast_ascFactorial : (a.ascFactorial b : S) = (ascPochhammer S b).eval (a : S) := by
  rw [← ascPochhammer_nat_eq_ascFactorial, ascPochhammer_eval_cast]
theorem cast_descFactorial :
    (a.descFactorial b : S) = (ascPochhammer S b).eval (a - (b - 1) : S) := by
  rw [← ascPochhammer_eval_cast, ascPochhammer_nat_eq_descFactorial]
  induction' b with b
  · simp
  · simp_rw [add_succ, Nat.add_one_sub_one]
    obtain h | h := le_total a b
    · rw [descFactorial_of_lt (lt_succ_of_le h), descFactorial_of_lt (lt_succ_of_le _)]
      rw [tsub_eq_zero_iff_le.mpr h, zero_add]
    · rw [tsub_add_cancel_of_le h]
theorem cast_factorial : (a ! : S) = (ascPochhammer S a).eval 1 := by
  rw [← one_ascFactorial, cast_ascFactorial, cast_one]
end Semiring
section Ring
variable [Ring S] (a b : ℕ)
theorem cast_descFactorial_two : (a.descFactorial 2 : S) = a * (a - 1) := by
  rw [cast_descFactorial]
  cases a
  · simp
  · rw [succ_sub_succ, tsub_zero, cast_succ, add_sub_cancel_right, ascPochhammer_succ_right,
      ascPochhammer_one, Polynomial.X_mul, Polynomial.eval_mul_X, Polynomial.eval_add,
      Polynomial.eval_X, cast_one, Polynomial.eval_one]
end Ring
end Nat