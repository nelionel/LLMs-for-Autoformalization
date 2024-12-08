import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.ZMod.Basic
open Finset Nat
namespace ZMod
theorem cast_descFactorial {n p : ℕ} (h : n ≤ p) :
    (descFactorial (p - 1) n : ZMod p) = (-1) ^ n * n ! := by
  rw [descFactorial_eq_prod_range, ← prod_range_add_one_eq_factorial]
  simp only [cast_prod]
  nth_rw 2 [← card_range n]
  rw [pow_card_mul_prod]
  refine prod_congr rfl ?_
  intro x hx
  rw [← tsub_add_eq_tsub_tsub_swap,
    Nat.cast_sub <| Nat.le_trans (Nat.add_one_le_iff.mpr (List.mem_range.mp hx)) h,
    CharP.cast_eq_zero, zero_sub, cast_succ, neg_add_rev, mul_add, neg_mul, one_mul,
    mul_one, add_comm]
end ZMod