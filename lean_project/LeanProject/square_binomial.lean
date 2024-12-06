import tactic

example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
begin
  rw pow_two,
  rw add_mul,
  rw mul_add,
  rw mul_add,
  rw mul_add,
  ring,
end