import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Mathlib.Tactic.StacksAttribute
assert_not_exists DivisionMonoid.toDivInvOneMonoid
assert_not_exists mul_rotate
universe u v
variable {α : Type u} {R : Type v}
open Function
class Distrib (R : Type*) extends Mul R, Add R where
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
class LeftDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
class RightDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
instance (priority := 100) Distrib.leftDistribClass (R : Type*) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩
instance (priority := 100) Distrib.rightDistribClass (R : Type*) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩
theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c
alias mul_add := left_distrib
theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c
alias add_mul := right_distrib
theorem distrib_three_right [Mul R] [Add R] [RightDistribClass R] (a b c d : R) :
    (a + b + c) * d = a * d + b * d + c * d := by simp [right_distrib]
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α
class NonUnitalRing (α : Type*) extends NonUnitalNonAssocRing α, NonUnitalSemiring α
class NonAssocRing (α : Type*) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α
class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
section DistribMulOneClass
variable [Add α] [MulOneClass α]
theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mul, one_mul]
theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_add, mul_one]
theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mul, one_mul]
theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_add, mul_one]
end DistribMulOneClass
section NonAssocSemiring
variable [NonAssocSemiring α]
theorem two_mul (n : α) : 2 * n = n + n :=
  (congrArg₂ _ one_add_one_eq_two.symm rfl).trans <| (right_distrib 1 1 n).trans (by rw [one_mul])
theorem mul_two (n : α) : n * 2 = n + n :=
  (congrArg₂ _ rfl one_add_one_eq_two.symm).trans <| (left_distrib n 1 1).trans (by rw [mul_one])
end NonAssocSemiring
section MulZeroClass
variable [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α)
lemma ite_zero_mul : ite P a 0 * b = ite P (a * b) 0 := by simp
lemma mul_ite_zero : a * ite P b 0 = ite P (a * b) 0 := by simp
lemma ite_zero_mul_ite_zero : ite P a 0 * ite Q b 0 = ite (P ∧ Q) (a * b) 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]
end MulZeroClass
theorem mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by simp
theorem boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by simp
class NonUnitalNonAssocCommSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, CommMagma α
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α
class CommSemiring (R : Type u) extends Semiring R, CommMonoid R
instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }
section CommSemiring
variable [CommSemiring α]
theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]
lemma add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [sq, add_mul_self_eq]
lemma add_sq' (a b : α) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq, add_assoc, add_comm _ (b ^ 2), add_assoc]
alias add_pow_two := add_sq
end CommSemiring
section HasDistribNeg
class HasDistribNeg (α : Type*) [Mul α] extends InvolutiveNeg α where
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  mul_neg : ∀ x y : α, x * -y = -(x * y)
section Mul
variable [Mul α] [HasDistribNeg α]
@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _
@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _
theorem neg_mul_neg (a b : α) : -a * -b = a * b := by simp
theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm
theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm
theorem neg_mul_comm (a b : α) : -a * b = a * -b := by simp
end Mul
section MulOneClass
variable [MulOneClass α] [HasDistribNeg α]
theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by simp
theorem mul_neg_one (a : α) : a * -1 = -a := by simp
theorem neg_one_mul (a : α) : -1 * a = -a := by simp
end MulOneClass
section MulZeroClass
variable [MulZeroClass α] [HasDistribNeg α]
instance (priority := 100) MulZeroClass.negZeroClass : NegZeroClass α where
  __ := inferInstanceAs (Zero α); __ := inferInstanceAs (InvolutiveNeg α)
  neg_zero := by rw [← zero_mul (0 : α), ← neg_mul, mul_zero, mul_zero]
end MulZeroClass
end HasDistribNeg
section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing α]
instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg := Neg.neg
  neg_neg := neg_neg
  neg_mul a b := eq_neg_of_add_eq_zero_left <| by rw [← right_distrib, neg_add_cancel, zero_mul]
  mul_neg a b := eq_neg_of_add_eq_zero_left <| by rw [← left_distrib, neg_add_cancel, mul_zero]
theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)
alias mul_sub := mul_sub_left_distrib
theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c
alias sub_mul := mul_sub_right_distrib
end NonUnitalNonAssocRing
section NonAssocRing
variable [NonAssocRing α]
theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [sub_mul, one_mul]
theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]
theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]
theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]
end NonAssocRing
section Ring
variable [Ring α]
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ring α› with }
instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  { ‹Ring α› with }
instance (priority := 200) : Semiring α :=
  { ‹Ring α› with }
end Ring
class NonUnitalNonAssocCommRing (α : Type u)
  extends NonUnitalNonAssocRing α, NonUnitalNonAssocCommSemiring α
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, NonUnitalNonAssocCommRing α
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }
class CommRing (α : Type u) extends Ring α, CommMonoid α
instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }
instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }
instance (priority := 100) CommRing.toAddCommGroupWithOne [s : CommRing α] :
    AddCommGroupWithOne α :=
  { s with }
@[stacks 09FE]
class IsDomain (α : Type u) [Semiring α] extends IsCancelMulZero α, Nontrivial α : Prop