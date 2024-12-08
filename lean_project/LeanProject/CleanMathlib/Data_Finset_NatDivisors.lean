import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.NumberTheory.Divisors
open Nat Finset
open scoped Pointwise
lemma Nat.divisors_mul (m n : ℕ) : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, dvd_mul, mul_ne_zero_iff, ← exists_and_left, ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]
@[simps]
def Nat.divisorsHom : ℕ →* Finset ℕ where
  toFun := Nat.divisors
  map_mul' := divisors_mul
  map_one' := divisors_one
lemma Nat.Prime.divisors_sq {p : ℕ} (hp : p.Prime) : (p ^ 2).divisors = {p ^ 2, p, 1} := by
  simp [divisors_prime_pow hp, range_succ]
lemma List.nat_divisors_prod (l : List ℕ) : divisors l.prod = (l.map divisors).prod :=
  map_list_prod Nat.divisorsHom l
lemma Multiset.nat_divisors_prod (s : Multiset ℕ) : divisors s.prod = (s.map divisors).prod :=
  map_multiset_prod Nat.divisorsHom s
lemma Finset.nat_divisors_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    divisors (∏ i ∈ s, f i) = ∏ i ∈ s, divisors (f i) :=
  map_prod Nat.divisorsHom f s