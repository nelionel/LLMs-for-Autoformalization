import Mathlib.Tactic.Ring
def hyperoperation : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k + 1
  | 1, m, 0 => m
  | 2, _, 0 => 0
  | _ + 3, _, 0 => 1
  | n + 1, m, k + 1 => hyperoperation n m (hyperoperation (n + 1) m k)
@[simp]
theorem hyperoperation_zero (m : ℕ) : hyperoperation 0 m = Nat.succ :=
  funext fun k => by rw [hyperoperation, Nat.succ_eq_add_one]
theorem hyperoperation_ge_three_eq_one (n m : ℕ) : hyperoperation (n + 3) m 0 = 1 := by
  rw [hyperoperation]
theorem hyperoperation_recursion (n m k : ℕ) :
    hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) := by
  rw [hyperoperation]
@[simp]
theorem hyperoperation_one : hyperoperation 1 = (· + ·) := by
  ext m k
  induction' k with bn bih
  · rw [Nat.add_zero m, hyperoperation]
  · rw [hyperoperation_recursion, bih, hyperoperation_zero]
    exact Nat.add_assoc m bn 1
@[simp]
theorem hyperoperation_two : hyperoperation 2 = (· * ·) := by
  ext m k
  induction' k with bn bih
  · rw [hyperoperation]
    exact (Nat.mul_zero m).symm
  · rw [hyperoperation_recursion, hyperoperation_one, bih]
    dsimp only
    nth_rewrite 1 [← mul_one m]
    rw [← mul_add, add_comm]
@[simp]
theorem hyperoperation_three : hyperoperation 3 = (· ^ ·) := by
  ext m k
  induction' k with bn bih
  · rw [hyperoperation_ge_three_eq_one]
    exact (pow_zero m).symm
  · rw [hyperoperation_recursion, hyperoperation_two, bih]
    exact (pow_succ' m bn).symm
theorem hyperoperation_ge_two_eq_self (n m : ℕ) : hyperoperation (n + 2) m 1 = m := by
  induction' n with nn nih
  · rw [hyperoperation_two]
    ring
  · rw [hyperoperation_recursion, hyperoperation_ge_three_eq_one, nih]
theorem hyperoperation_two_two_eq_four (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 := by
  induction' n with nn nih
  · rw [hyperoperation_one]
  · rw [hyperoperation_recursion, hyperoperation_ge_two_eq_self, nih]
theorem hyperoperation_ge_three_one (n : ℕ) : ∀ k : ℕ, hyperoperation (n + 3) 1 k = 1 := by
  induction' n with nn nih
  · intro k
    rw [hyperoperation_three]
    dsimp
    rw [one_pow]
  · intro k
    cases k
    · rw [hyperoperation_ge_three_eq_one]
    · rw [hyperoperation_recursion, nih]
theorem hyperoperation_ge_four_zero (n k : ℕ) :
    hyperoperation (n + 4) 0 k = if Even k then 1 else 0 := by
  induction' k with kk kih
  · rw [hyperoperation_ge_three_eq_one]
    simp only [even_zero, if_true]
  · rw [hyperoperation_recursion]
    rw [kih]
    simp_rw [Nat.even_add_one]
    split_ifs
    · exact hyperoperation_ge_two_eq_self (n + 1) 0
    · exact hyperoperation_ge_three_eq_one n 0