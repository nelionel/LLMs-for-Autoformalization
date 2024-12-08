import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Algebraize
open Polynomial
section Ring
variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)
def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=
  ∃ p : R[X], Monic p ∧ eval₂ f x p = 0
@[algebraize Algebra.IsIntegral.mk]
def RingHom.IsIntegral (f : R →+* A) :=
  ∀ x : A, f.IsIntegralElem x
variable [Algebra R A] (R)
def IsIntegral (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x
end Ring