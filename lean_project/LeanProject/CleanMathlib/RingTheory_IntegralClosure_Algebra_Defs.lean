import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
open Polynomial Submodule
section Ring
variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)
variable [Algebra R A] (R)
variable (A)
protected class Algebra.IsIntegral : Prop where
  isIntegral : ∀ x : A, IsIntegral R x
variable {R A}
lemma Algebra.isIntegral_def : Algebra.IsIntegral R A ↔ ∀ x : A, IsIntegral R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
end Ring