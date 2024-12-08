import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Spread
namespace Function
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
namespace Injective
variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]
@[to_additive "A type endowed with `+` is an additive semigroup, if it admits an
injective map that preserves `+` to an additive semigroup."]
protected abbrev semigroup [Semigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₁ :=
  { ‹Mul M₁› with mul_assoc := fun x y z => hf <| by rw [mul, mul, mul, mul, mul_assoc] }
@[to_additive 
"A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup."]
protected abbrev commMagma [CommMagma M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMagma M₁ where
  mul_comm x y := hf <| by rw [mul, mul, mul_comm]
@[to_additive
"A type endowed with `+` is an additive commutative semigroup,if it admits
an injective map that preserves `+` to an additive commutative semigroup."]
protected abbrev commSemigroup [CommSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₁ where
  toSemigroup := hf.semigroup f mul
  __ := hf.commMagma f mul
@[to_additive "A type endowed with `+` is an additive left cancel
semigroup, if it admits an injective map that preserves `+` to an additive left cancel semigroup."]
protected abbrev leftCancelSemigroup [LeftCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftCancelSemigroup M₁ :=
  { hf.semigroup f mul with
    mul_left_cancel := fun x y z H => hf <| (mul_right_inj (f x)).1 <| by rw [← mul, ← mul, H] }
@[to_additive "A type endowed with `+` is an additive right
cancel semigroup, if it admits an injective map that preserves `+` to an additive right cancel
semigroup."]
protected abbrev rightCancelSemigroup [RightCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightCancelSemigroup M₁ :=
  { hf.semigroup f mul with
    mul_right_cancel := fun x y z H => hf <| (mul_left_inj (f y)).1 <| by rw [← mul, ← mul, H] }
variable [One M₁]
@[to_additive
"A type endowed with `0` and `+` is an `AddZeroClass`, if it admits an
injective map that preserves `0` and `+` to an `AddZeroClass`."]
protected abbrev mulOneClass [MulOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₁ :=
  { ‹One M₁›, ‹Mul M₁› with
    one_mul := fun x => hf <| by rw [mul, one, one_mul],
    mul_one := fun x => hf <| by rw [mul, one, mul_one] }
variable [Pow M₁ ℕ]
@[to_additive
"A type endowed with `0` and `+` is an additive monoid, if it admits an
injective map that preserves `0` and `+` to an additive monoid. See note
[reducible non-instances]."]
protected abbrev monoid [Monoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₁ :=
  { hf.mulOneClass f one mul, hf.semigroup f mul with
    npow := fun n x => x ^ n,
    npow_zero := fun x => hf <| by rw [npow, one, pow_zero],
    npow_succ := fun n x => hf <| by rw [npow, pow_succ, mul, npow] }
protected abbrev addMonoidWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [NatCast M₁]
    [AddMonoidWithOne M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne M₁ :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := hf (by rw [natCast, Nat.cast_zero, zero]),
    natCast_succ := fun n => hf (by rw [natCast, Nat.cast_succ, add, one, natCast]), one := 1 }
@[to_additive
"A type endowed with `0` and `+` is an additive left cancel monoid, if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected abbrev leftCancelMonoid [LeftCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : LeftCancelMonoid M₁ :=
  { hf.leftCancelSemigroup f mul, hf.monoid f one mul npow with }
@[to_additive
"A type endowed with `0` and `+` is an additive left cancel monoid,if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected abbrev rightCancelMonoid [RightCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : RightCancelMonoid M₁ :=
  { hf.rightCancelSemigroup f mul, hf.monoid f one mul npow with }
@[to_additive
"A type endowed with `0` and `+` is an additive left cancel monoid,if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected abbrev cancelMonoid [CancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelMonoid M₁ :=
  { hf.leftCancelMonoid f one mul npow, hf.rightCancelMonoid f one mul npow with }
@[to_additive
"A type endowed with `0` and `+` is an additive commutative monoid, if it
admits an injective map that preserves `0` and `+` to an additive commutative monoid."]
protected abbrev commMonoid [CommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₁ :=
  { hf.monoid f one mul npow, hf.commSemigroup f mul with }
protected abbrev addCommMonoidWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [NatCast M₁]
    [AddCommMonoidWithOne M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne M₁ where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)
@[to_additive
"A type endowed with `0` and `+` is an additive cancel commutative monoid,
if it admits an injective map that preserves `0` and `+` to an additive cancel commutative monoid."]
protected abbrev cancelCommMonoid [CancelCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelCommMonoid M₁ :=
  { hf.leftCancelSemigroup f mul, hf.commMonoid f one mul npow with }
@[to_additive
"A type has an involutive negation if it admits a surjective map that
preserves `-` to a type which has an involutive negation."]
protected abbrev involutiveInv {M₁ : Type*} [Inv M₁] [InvolutiveInv M₂] (f : M₁ → M₂)
    (hf : Injective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₁ where
  inv := Inv.inv
  inv_inv x := hf <| by rw [inv, inv, inv_inv]
variable [Inv M₁]
@[to_additive
"A type endowed with `0` and unary `-` is an `NegZeroClass`, if it admits an
injective map that preserves `0` and unary `-` to an `NegZeroClass`."]
protected abbrev invOneClass [InvOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) : InvOneClass M₁ :=
  { ‹One M₁›, ‹Inv M₁› with
    inv_one := hf <| by rw [inv, one, inv_one] }
variable [Div M₁] [Pow M₁ ℤ]
@[to_additive subNegMonoid
"A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `SubNegMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]` and `[SMul ℤ M₁]`
arguments."]
protected abbrev divInvMonoid [DivInvMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₁ :=
  { hf.monoid f one mul npow, ‹Inv M₁›, ‹Div M₁› with
    zpow := fun n x => x ^ n,
    zpow_zero' := fun x => hf <| by rw [zpow, zpow_zero, one],
    zpow_succ' := fun n x => hf <| by rw [zpow, mul, zpow_natCast, pow_succ, zpow, zpow_natCast],
    zpow_neg' := fun n x => hf <| by rw [zpow, zpow_negSucc, inv, zpow, zpow_natCast],
    div_eq_mul_inv := fun x y => hf <| by rw [div, mul, inv, div_eq_mul_inv] }
@[to_additive
"A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegZeroMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and binary
`-` to a `SubNegZeroMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]` and
`[SMul ℤ M₁]` arguments."]
protected abbrev divInvOneMonoid [DivInvOneMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvOneMonoid M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow, hf.invOneClass f one inv with }
@[to_additive
"A type endowed with `0`, `+`, unary `-`, and binary `-`
is a `SubtractionMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and
binary `-` to a `SubtractionMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]`
and `[SMul ℤ M₁]` arguments."]
protected abbrev divisionMonoid [DivisionMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionMonoid M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow, hf.involutiveInv f inv with
    mul_inv_rev := fun x y => hf <| by rw [inv, mul, mul_inv_rev, mul, inv, inv],
    inv_eq_of_mul := fun x y h => hf <| by
      rw [inv, inv_eq_of_mul_eq_one_right (by rw [← mul, h, one])] }
@[to_additive subtractionCommMonoid
"A type endowed with `0`, `+`, unary `-`, and binary
`-` is a `SubtractionCommMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`,
and binary `-` to a `SubtractionCommMonoid`. This version takes custom `nsmul` and `zsmul` as
`[SMul ℕ M₁]` and `[SMul ℤ M₁]` arguments."]
protected abbrev divisionCommMonoid [DivisionCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionCommMonoid M₁ :=
  { hf.divisionMonoid f one mul inv div npow zpow, hf.commSemigroup f mul with }
@[to_additive
"A type endowed with `0` and `+` is an additive group, if it admits an
injective map that preserves `0` and `+` to an additive group."]
protected abbrev group [Group M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow with
    inv_mul_cancel := fun x => hf <| by rw [mul, inv, inv_mul_cancel, one] }
protected abbrev addGroupWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [Neg M₁] [Sub M₁]
    [SMul ℤ M₁] [NatCast M₁] [IntCast M₁] [AddGroupWithOne M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne M₁ :=
  { hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul),
    hf.addMonoidWithOne f zero one add nsmul natCast with
    intCast := Int.cast,
    intCast_ofNat := fun n => hf (by rw [natCast, ← Int.cast, intCast, Int.cast_natCast]),
    intCast_negSucc := fun n => hf (by rw [intCast, neg, natCast, Int.cast_negSucc] ) }
@[to_additive
"A type endowed with `0` and `+` is an additive commutative group, if it
admits an injective map that preserves `0` and `+` to an additive commutative group."]
protected abbrev commGroup [CommGroup M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₁ :=
  { hf.commMonoid f one mul npow, hf.group f one mul inv div npow zpow with }
protected abbrev addCommGroupWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [Neg M₁] [Sub M₁]
    [SMul ℤ M₁] [NatCast M₁] [IntCast M₁] [AddCommGroupWithOne M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne M₁ :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }
end Injective
namespace Surjective
variable {M₁ : Type*} {M₂ : Type*} [Mul M₂]
@[to_additive
"A type endowed with `+` is an additive semigroup, if it admits a
surjective map that preserves `+` from an additive semigroup."]
protected abbrev semigroup [Semigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₂ :=
  { ‹Mul M₂› with mul_assoc := hf.forall₃.2 fun x y z => by simp only [← mul, mul_assoc] }
@[to_additive
"A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup."]
protected abbrev commMagma [CommMagma M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMagma M₂ where
  mul_comm := hf.forall₂.2 fun x y => by rw [← mul, ← mul, mul_comm]
@[to_additive
"A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup."]
protected abbrev commSemigroup [CommSemigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₂ where
  toSemigroup := hf.semigroup f mul
  __ := hf.commMagma f mul
variable [One M₂]
@[to_additive
"A type endowed with `0` and `+` is an `AddZeroClass`, if it admits a
surjective map that preserves `0` and `+` to an `AddZeroClass`."]
protected abbrev mulOneClass [MulOneClass M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₂ :=
  { ‹One M₂›, ‹Mul M₂› with
    one_mul := hf.forall.2 fun x => by rw [← one, ← mul, one_mul],
    mul_one := hf.forall.2 fun x => by rw [← one, ← mul, mul_one] }
variable [Pow M₂ ℕ]
@[to_additive
"A type endowed with `0` and `+` is an additive monoid, if it admits a
surjective map that preserves `0` and `+` to an additive monoid. This version takes a custom `nsmul`
as a `[SMul ℕ M₂]` argument."]
protected abbrev monoid [Monoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₂ :=
  { hf.semigroup f mul, hf.mulOneClass f one mul with
    npow := fun n x => x ^ n,
    npow_zero := hf.forall.2 fun x => by dsimp only; rw [← npow, pow_zero, ← one],
    npow_succ := fun n => hf.forall.2 fun x => by
      dsimp only
      rw [← npow, pow_succ, ← npow, ← mul] }
protected abbrev addMonoidWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [SMul ℕ M₂] [NatCast M₂]
    [AddMonoidWithOne M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne M₂ :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := by rw [← Nat.cast, ← natCast, Nat.cast_zero, zero]
    natCast_succ := fun n => by rw [← Nat.cast, ← natCast, Nat.cast_succ, add, one, natCast]
    one := 1 }
@[to_additive
"A type endowed with `0` and `+` is an additive commutative monoid, if it
admits a surjective map that preserves `0` and `+` to an additive commutative monoid."]
protected abbrev commMonoid [CommMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₂ :=
  { hf.commSemigroup f mul, hf.monoid f one mul npow with }
protected abbrev addCommMonoidWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [SMul ℕ M₂] [NatCast M₂]
    [AddCommMonoidWithOne M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne M₂ where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)
@[to_additive
"A type has an involutive negation if it admits a surjective map that
preserves `-` to a type which has an involutive negation."]
protected abbrev involutiveInv {M₂ : Type*} [Inv M₂] [InvolutiveInv M₁] (f : M₁ → M₂)
    (hf : Surjective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₂ where
  inv := Inv.inv
  inv_inv := hf.forall.2 fun x => by rw [← inv, ← inv, inv_inv]
variable [Inv M₂] [Div M₂] [Pow M₂ ℤ]
@[to_additive subNegMonoid
"A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegMonoid` if it admits a surjective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `SubNegMonoid`."]
protected abbrev divInvMonoid [DivInvMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₂ :=
  { hf.monoid f one mul npow, ‹Div M₂›, ‹Inv M₂› with
    zpow := fun n x => x ^ n,
    zpow_zero' := hf.forall.2 fun x => by dsimp only; rw [← zpow, zpow_zero, ← one],
    zpow_succ' := fun n => hf.forall.2 fun x => by
      dsimp only
      rw [← zpow, ← zpow, zpow_natCast, zpow_natCast, pow_succ, ← mul],
    zpow_neg' := fun n => hf.forall.2 fun x => by
      dsimp only
      rw [← zpow, ← zpow, zpow_negSucc, zpow_natCast, inv],
    div_eq_mul_inv := hf.forall₂.2 fun x y => by rw [← inv, ← mul, ← div, div_eq_mul_inv] }
@[to_additive
"A type endowed with `0` and `+` is an additive group, if it admits a
surjective map that preserves `0` and `+` to an additive group."]
protected abbrev group [Group M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₂ :=
  { hf.divInvMonoid f one mul inv div npow zpow with
    inv_mul_cancel := hf.forall.2 fun x => by rw [← inv, ← mul, inv_mul_cancel, one] }
protected abbrev addGroupWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [Neg M₂] [Sub M₂] [SMul ℕ M₂]
    [SMul ℤ M₂] [NatCast M₂] [IntCast M₂] [AddGroupWithOne M₁] (f : M₁ → M₂) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne M₂ :=
  { hf.addMonoidWithOne f zero one add nsmul natCast,
    hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul) with
    intCast := Int.cast,
    intCast_ofNat := fun n => by rw [← Int.cast, ← intCast, Int.cast_natCast, natCast],
    intCast_negSucc := fun n => by
      rw [← Int.cast, ← intCast, Int.cast_negSucc, neg, natCast] }
@[to_additive
"A type endowed with `0` and `+` is an additive commutative group, if it
admits a surjective map that preserves `0` and `+` to an additive commutative group."]
protected abbrev commGroup [CommGroup M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₂ :=
  { hf.commMonoid f one mul npow, hf.group f one mul inv div npow zpow with }
protected abbrev addCommGroupWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [Neg M₂] [Sub M₂] [SMul ℕ M₂]
    [SMul ℤ M₂] [NatCast M₂] [IntCast M₂] [AddCommGroupWithOne M₁] (f : M₁ → M₂) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne M₂ :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }
end Surjective
end Function