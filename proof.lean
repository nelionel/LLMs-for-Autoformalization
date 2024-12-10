```lean
import Mathlib.Data.Nat.Basic

open Nat

theorem main_goal : ∀ f : ℕ → ℕ, (∀ a b : ℕ, f (a^2 + b^2) = f a * f b) ∧ (∀ a : ℕ, f (a^2) = f a ^ 2) → (∀ n : ℕ, f n = 1) :=
begin
  intros f ⟨h1, h2⟩,
  have f0 : f 0 = 1,
  { have h := h2 0,
    rw [pow_two, zero_mul] at h,
    exact h, },
  have f1 : f 1 = 1,
  { have h := h2 1,
    rw [pow_two, one_mul] at h,
    exact h, },
  have f2 : f 2 = 1,
  { have h := h1 1 1,
    rw [one_pow, one_pow, add_self_eq_two, f1, mul_one] at h,
    exact h, },
  have f_sq : ∀ a : ℕ, f a = 1,
  { intro a,
    induction a with n ih,
    { exact f0, },
    { cases n,
      { exact f1, },
      { cases n,
        { exact f2, },
        { have h := h1 (n + 2) 0,
          rw [zero_pow (by decide), f0, mul_one] at h,
          exact h, } } } },
  exact f_sq,
end
```