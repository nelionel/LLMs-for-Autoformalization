import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
noncomputable section

theorem exercise_10_4_6 {R : Type*} [CommRing R]
  [NoZeroDivisors R] (I J : Ideal R) (x : ↑(I ⊓ J)) :
  IsNilpotent ((Ideal.Quotient.mk (I*J)) x) :=
begin
  let x_ij := Ideal.Quotient.mk (I*J) x,
  have hxI : x ∈ I := Ideal.mem_inf.mp x.2.left,
  have hxJ : x ∈ J := Ideal.mem_inf.mp x.2.right,
  -- Since x ∈ I ∩ J, we have x ∈ I and x ∈ J, hence x² ∈ IJ
  have hx2 : x * x ∈ I * J,
  { apply Ideal.mul_mem_mul; assumption },

  -- In the quotient R / IJ, this means [x]² = [0]
  show ∃ n : ℕ, x_ij ^ n = 0,
  use 2,
  rw [pow_two, Ideal.Quotient.eq_zero_iff_mem],
  exact hx2,
end