import Mathlib.Algebra.Polynomial.AlgebraMap
assert_not_exists IsIntegralClosure
assert_not_exists LinearIndependent
assert_not_exists LocalRing
assert_not_exists MvPolynomial
open Polynomial
section Pi
variable (R S T : Type*)
def Polynomial.hasSMulPi [Semiring R] [SMul R S] : SMul R[X] (R → S) :=
  ⟨fun p f x => eval x p • f x⟩
noncomputable def Polynomial.hasSMulPi' [CommSemiring R] [Semiring S] [Algebra R S]
    [SMul S T] : SMul R[X] (S → T) :=
  ⟨fun p f x => aeval x p • f x⟩
attribute [local instance] Polynomial.hasSMulPi Polynomial.hasSMulPi'
@[simp]
theorem polynomial_smul_apply [Semiring R] [SMul R S] (p : R[X]) (f : R → S) (x : R) :
    (p • f) x = eval x p • f x :=
  rfl
@[simp]
theorem polynomial_smul_apply' [CommSemiring R] [Semiring S] [Algebra R S] [SMul S T]
    (p : R[X]) (f : S → T) (x : S) : (p • f) x = aeval x p • f x :=
  rfl
variable [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra S T]
noncomputable def Polynomial.algebraPi : Algebra R[X] (S → T) :=
  { Polynomial.hasSMulPi' R S T with
    toFun := fun p z => algebraMap S T (aeval z p)
    map_one' := by
      funext z
      simp only [Polynomial.aeval_one, Pi.one_apply, map_one]
    map_mul' := fun f g => by
      funext z
      simp only [Pi.mul_apply, map_mul]
    map_zero' := by
      funext z
      simp only [Polynomial.aeval_zero, Pi.zero_apply, map_zero]
    map_add' := fun f g => by
      funext z
      simp only [Polynomial.aeval_add, Pi.add_apply, map_add]
    commutes' := fun p f => by
      funext z
      exact mul_comm _ _
    smul_def' := fun p f => by
      funext z
      simp only [polynomial_smul_apply', Algebra.algebraMap_eq_smul_one, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul] }
attribute [local instance] Polynomial.algebraPi
@[simp]
theorem Polynomial.algebraMap_pi_eq_aeval :
    (algebraMap R[X] (S → T) : R[X] → S → T) = fun p z => algebraMap _ _ (aeval z p) :=
  rfl
@[simp]
theorem Polynomial.algebraMap_pi_self_eq_eval :
    (algebraMap R[X] (R → R) : R[X] → R → R) = fun p z => eval z p :=
  rfl
end Pi