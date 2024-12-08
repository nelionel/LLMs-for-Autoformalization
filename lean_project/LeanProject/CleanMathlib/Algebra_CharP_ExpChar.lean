import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharP.Lemmas
open ExpChar
universe u
variable (R : Type u)
section frobenius
section CommSemiring
variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →* S) (g : R →+* S) (p m n : ℕ)
  [ExpChar R p] [ExpChar S p] (x y : R)
variable (S)
nonrec def LinearMap.frobenius [Algebra R S] : S →ₛₗ[frobenius R p] S where
  __ := frobenius S p
  map_smul' r s := show frobenius S p _ = _ by
    simp_rw [Algebra.smul_def, map_mul, ← (algebraMap R S).map_frobenius]; rfl
nonrec def LinearMap.iterateFrobenius [Algebra R S] : S →ₛₗ[iterateFrobenius R p n] S where
  __ := iterateFrobenius S p n
  map_smul' f s := show iterateFrobenius S p n _ = _ by
    simp_rw [iterateFrobenius_def, Algebra.smul_def, mul_pow, ← map_pow]; rfl
theorem LinearMap.frobenius_def [Algebra R S] (x : S) : frobenius R S p x = x ^ p := rfl
theorem LinearMap.iterateFrobenius_def [Algebra R S] (n : ℕ) (x : S) :
    iterateFrobenius R S p n x = x ^ p ^ n := rfl
theorem frobenius_zero : frobenius R p 0 = 0 :=
  (frobenius R p).map_zero
theorem frobenius_add : frobenius R p (x + y) = frobenius R p x + frobenius R p y :=
  (frobenius R p).map_add x y
theorem frobenius_natCast (n : ℕ) : frobenius R p n = n :=
  map_natCast (frobenius R p) n
@[deprecated (since := "2024-04-17")]
alias frobenius_nat_cast := frobenius_natCast
end CommSemiring
end frobenius