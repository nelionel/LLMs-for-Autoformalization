import Mathlib.Algebra.MvPolynomial.Basic
namespace MvPolynomial
open Function
variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]
noncomputable def ACounit : MvPolynomial B A →ₐ[A] B :=
  aeval id
variable {B}
@[simp]
theorem ACounit_X (b : B) : ACounit A B (X b) = b :=
  aeval_X _ b
variable {A} (B)
theorem ACounit_C (a : A) : ACounit A B (C a) = algebraMap A B a :=
  aeval_C _ a
variable (A)
theorem ACounit_surjective : Surjective (ACounit A B) := fun b => ⟨X b, ACounit_X A b⟩
noncomputable def counit : MvPolynomial R ℤ →+* R :=
  (ACounit ℤ R).toRingHom
noncomputable def counitNat : MvPolynomial A ℕ →+* A :=
  ACounit ℕ A
theorem counit_surjective : Surjective (counit R) :=
  ACounit_surjective ℤ R
theorem counitNat_surjective : Surjective (counitNat A) :=
  ACounit_surjective ℕ A
theorem counit_C (n : ℤ) : counit R (C n) = n :=
  ACounit_C _ _
theorem counitNat_C (n : ℕ) : counitNat A (C n) = n :=
  ACounit_C _ _
variable {R A}
@[simp]
theorem counit_X (r : R) : counit R (X r) = r :=
  ACounit_X _ _
@[simp]
theorem counitNat_X (a : A) : counitNat A (X a) = a :=
  ACounit_X _ _
end MvPolynomial