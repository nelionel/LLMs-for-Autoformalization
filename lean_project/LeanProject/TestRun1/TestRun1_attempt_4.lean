theorem main_goal (f : ℕ → ℕ)
  (h1 : ∀ a b : ℕ, a > 0 → b > 0 → f (a^2 + b^2) = f a * f b)
  (h2 : ∀ a : ℕ, a > 0 → f (a^2) = f a ^ 2) :
  ∀ n : ℕ, f n = 1 :=
sorry