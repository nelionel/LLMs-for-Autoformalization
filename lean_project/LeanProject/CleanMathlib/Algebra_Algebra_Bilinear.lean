import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.GroupPower.IterateHom
import Mathlib.LinearAlgebra.TensorProduct.Basic
open TensorProduct Module
namespace LinearMap
section NonUnitalNonAssoc
variable (R A : Type*)
section one_side
variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
section left
variable {A} [SMulCommClass R A A]
def mulLeft (a : A) : A →ₗ[R] A where
  toFun := (a * ·)
  map_add' := mul_add _
  map_smul' _ := mul_smul_comm _ _
@[simp]
theorem mulLeft_apply (a b : A) : mulLeft R a b = a * b := rfl
@[simp]
theorem mulLeft_toAddMonoidHom (a : A) : (mulLeft R a : A →+ A) = AddMonoidHom.mulLeft a := rfl
variable (A) in
@[simp]
theorem mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0 := ext fun _ => zero_mul _
end left
section right
variable {A} [IsScalarTower R A A]
def mulRight (b : A) : A →ₗ[R] A where
  toFun := (· * b)
  map_add' _ _ := add_mul _ _ _
  map_smul' _ _ := smul_mul_assoc _ _ _
@[simp]
theorem mulRight_apply (a b : A) : mulRight R a b = b * a := rfl
@[simp]
theorem mulRight_toAddMonoidHom (a : A) : (mulRight R a : A →+ A) = AddMonoidHom.mulRight a := rfl
variable (A) in
@[simp]
theorem mulRight_zero_eq_zero : mulRight R (0 : A) = 0 := ext fun _ => mul_zero _
end right
end one_side
variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]
@[simps!]
def mul : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm
noncomputable def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)
variable {A}
def mulLeftRight (ab : A × A) : A →ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)
variable {R}
@[simp]
theorem mul_apply' (a b : A) : mul R A a b = a * b :=
  rfl
@[simp]
theorem mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b :=
  rfl
@[simp]
theorem mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b :=
  rfl
end NonUnitalNonAssoc
section NonUnital
variable (R A B : Type*)
section one_side
variable [Semiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]
@[simp]
theorem mulLeft_mul [SMulCommClass R A A] (a b : A) :
    mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]
@[simp]
theorem mulRight_mul [IsScalarTower R A A] (a b : A) :
    mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]
end one_side
variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]
variable [SMulCommClass R B B] [IsScalarTower R B B]
def _root_.NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A where
  __ := mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _
variable {R A B}
@[simp]
theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = mul R A :=
  rfl
theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm
theorem map_mul_iff (f : A →ₗ[R] B) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f :=
  Iff.symm LinearMap.ext_iff₂
end NonUnital
section Semiring
variable (R A : Type*)
section one_side
variable [Semiring R] [Semiring A]
section left
variable [Module R A] [SMulCommClass R A A]
@[simp]
theorem mulLeft_one : mulLeft R (1 : A) = LinearMap.id := ext fun _ => one_mul _
@[simp]
theorem mulLeft_eq_zero_iff (a : A) : mulLeft R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · rw [← mul_one a, ← mulLeft_apply R a 1, h, LinearMap.zero_apply]
  · rw [h]
    exact mulLeft_zero_eq_zero _ _
@[simp]
theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, LinearMap.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, LinearMap.mul_eq_comp, pow_mulLeft]
end left
section right
variable [Module R A] [IsScalarTower R A A]
@[simp]
theorem mulRight_one : mulRight R (1 : A) = LinearMap.id := ext fun _ => mul_one _
@[simp]
theorem mulRight_eq_zero_iff (a : A) : mulRight R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · rw [← one_mul a, ← mulRight_apply R a 1, h, LinearMap.zero_apply]
  · rw [h]
    exact mulRight_zero_eq_zero _ _
@[simp]
theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, LinearMap.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, LinearMap.mul_eq_comp, pow_mulRight]
end right
end one_side
variable [CommSemiring R] [Semiring A] [Algebra R A]
def _root_.Algebra.lmul : A →ₐ[R] End R A where
  __ := NonUnitalAlgHom.lmul R A
  map_one' := mulLeft_one _ _
  commutes' r := ext fun a => (Algebra.smul_def r a).symm
variable {R A}
@[simp]
theorem _root_.Algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = mul R A :=
  rfl
theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) :=
  fun a₁ a₂ h ↦ by simpa using DFunLike.congr_fun h 1
theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End_isUnit_iff, Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective
theorem toSpanSingleton_eq_algebra_linearMap : toSpanSingleton R A 1 = Algebra.linearMap R A := by
  ext; simp
end Semiring
section Ring
variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
@[deprecated mul_right_injective₀ (since := "2024-11-18")]
theorem mulLeft_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) :
    Function.Injective (mulLeft R x) :=
  mul_right_injective₀ hx
@[deprecated mul_left_injective₀ (since := "2024-11-18")]
theorem mulRight_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) :
    Function.Injective (mulRight R x) :=
  mul_left_injective₀ hx
@[deprecated mul_right_injective₀ (since := "2024-11-18")]
theorem mul_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (mul R A x) :=
   mul_right_injective₀ hx
end Ring
end LinearMap