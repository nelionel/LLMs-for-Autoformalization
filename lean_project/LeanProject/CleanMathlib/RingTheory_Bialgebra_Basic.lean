import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
suppress_compilation
universe u v
open scoped TensorProduct
class Bialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Algebra R A, Coalgebra R A where
  counit_one : counit 1 = 1
  mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
  comul_one : comul 1 = 1
  mul_compr₂_comul :
    (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A ⊗[R] A)).compl₁₂ comul comul
namespace Bialgebra
open Coalgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [Bialgebra R A]
lemma counit_mul (a b : A) : counit (R := R) (a * b) = counit a * counit b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_counit a) b
lemma comul_mul (a b : A) : comul (R := R) (a * b) = comul a * comul b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_comul a) b
attribute [simp] counit_one comul_one counit_mul comul_mul
def mk' (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    [Algebra R A] [C : Coalgebra R A] (counit_one : C.counit 1 = 1)
    (counit_mul : ∀ {a b}, C.counit (a * b) = C.counit a * C.counit b)
    (comul_one : C.comul 1 = 1)
    (comul_mul : ∀ {a b}, C.comul (a * b) = C.comul a * C.comul b) :
    Bialgebra R A where
  counit_one := counit_one
  mul_compr₂_counit := by ext; exact counit_mul
  comul_one := comul_one
  mul_compr₂_comul := by ext; exact comul_mul
variable (R A)
@[simps!]
def counitAlgHom : A →ₐ[R] R :=
  .ofLinearMap counit counit_one counit_mul
@[simps!]
def comulAlgHom : A →ₐ[R] A ⊗[R] A :=
  .ofLinearMap comul comul_one comul_mul
variable {R A}
@[simp] lemma counit_algebraMap (r : R) : counit (R := R) (algebraMap R A r) = r :=
  (counitAlgHom R A).commutes r
@[simp] lemma comul_algebraMap (r : R) :
    comul (R := R) (algebraMap R A r) = algebraMap R (A ⊗[R] A) r :=
  (comulAlgHom R A).commutes r
@[simp] lemma counit_natCast (n : ℕ) : counit (R := R) (n : A) = n :=
  map_natCast (counitAlgHom R A) _
@[simp] lemma comul_natCast (n : ℕ) : comul (R := R) (n : A) = n :=
  map_natCast (comulAlgHom R A) _
@[simp] lemma counit_pow (a : A) (n : ℕ) : counit (R := R) (a ^ n) = counit a ^ n :=
  map_pow (counitAlgHom R A) a n
@[simp] lemma comul_pow (a : A) (n : ℕ) : comul (R := R) (a ^ n) = comul a ^ n :=
  map_pow (comulAlgHom R A) a n
end Bialgebra
namespace CommSemiring
variable (R : Type u) [CommSemiring R]
open Bialgebra
noncomputable
instance toBialgebra : Bialgebra R R where
  mul_compr₂_counit := by ext; simp
  counit_one := rfl
  mul_compr₂_comul := by ext; simp
  comul_one := rfl
end CommSemiring