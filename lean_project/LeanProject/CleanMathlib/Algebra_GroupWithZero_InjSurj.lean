import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.GroupWithZero.NeZero
assert_not_exists DenselyOrdered
open Function
variable {M₀ G₀ M₀' G₀' : Type*}
section MulZeroClass
variable [MulZeroClass M₀]
protected abbrev Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  zero_mul a := hf <| by simp only [mul, zero, zero_mul]
  mul_zero a := hf <| by simp only [mul, zero, mul_zero]
protected abbrev Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  mul_zero := hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]
end MulZeroClass
section NoZeroDivisors
variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)
include hf zero mul
protected theorem Function.Injective.noZeroDivisors [NoZeroDivisors M₀'] : NoZeroDivisors M₀ :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} H ↦
      have : f a * f b = 0 := by rw [← mul, H, zero]
      (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
        (fun H => hf <| by rwa [zero]) fun H => hf <| by rwa [zero] }
protected theorem Function.Injective.isLeftCancelMulZero
    [IsLeftCancelMulZero M₀'] : IsLeftCancelMulZero M₀ :=
  { mul_left_cancel_of_ne_zero := fun Hne He => by
      have := congr_arg f He
      rw [mul, mul] at this
      exact hf (mul_left_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this) }
protected theorem Function.Injective.isRightCancelMulZero
    [IsRightCancelMulZero M₀'] : IsRightCancelMulZero M₀ :=
  { mul_right_cancel_of_ne_zero := fun Hne He => by
      have := congr_arg f He
      rw [mul, mul] at this
      exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this) }
end NoZeroDivisors
section MulZeroOneClass
variable [MulZeroOneClass M₀]
protected abbrev Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }
protected abbrev Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }
end MulZeroOneClass
section SemigroupWithZero
protected abbrev Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }
protected abbrev Function.Surjective.semigroupWithZero [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀']
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }
end SemigroupWithZero
section MonoidWithZero
protected abbrev Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }
protected abbrev Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }
protected abbrev Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }
protected abbrev Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }
end MonoidWithZero
section CancelMonoidWithZero
variable [CancelMonoidWithZero M₀]
protected abbrev Function.Injective.cancelMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelMonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with
    mul_left_cancel_of_ne_zero := fun hx H =>
      hf <| mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) <| by rw [← mul, ← mul, H],
    mul_right_cancel_of_ne_zero := fun hx H =>
      hf <| mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) <| by rw [← mul, ← mul, H] }
end CancelMonoidWithZero
section CancelCommMonoidWithZero
variable [CancelCommMonoidWithZero M₀]
protected abbrev Function.Injective.cancelCommMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀']
    [Pow M₀' ℕ] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelCommMonoidWithZero M₀' :=
  { hf.commMonoidWithZero f zero one mul npow, hf.cancelMonoidWithZero f zero one mul npow with }
end CancelCommMonoidWithZero
section GroupWithZero
variable [GroupWithZero G₀]
protected abbrev Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow,
    hf.divInvMonoid f one mul inv div npow zpow,
    pullback_nonzero f zero one with
    inv_zero := hf <| by rw [inv, zero, inv_zero],
    mul_inv_cancel := fun x hx => hf <| by
      rw [one, mul, inv, mul_inv_cancel₀ ((hf.ne_iff' zero).2 hx)] }
protected abbrev Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow, hf.divInvMonoid f one mul inv div npow zpow with
    inv_zero := by rw [← zero, ← inv, inv_zero],
    mul_inv_cancel := hf.forall.2 fun x hx => by
        rw [← inv, ← mul, mul_inv_cancel₀ (mt (congr_arg f) fun h ↦ hx (h.trans zero)), one]
    exists_pair_ne := ⟨0, 1, h01⟩ }
end GroupWithZero
section CommGroupWithZero
variable [CommGroupWithZero G₀]
protected abbrev Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.groupWithZero f zero one mul inv div npow zpow, hf.commSemigroup f mul with }
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    CommGroupWithZero G₀' :=
  { hf.groupWithZero h01 f zero one mul inv div npow zpow, hf.commSemigroup f mul with }
end CommGroupWithZero