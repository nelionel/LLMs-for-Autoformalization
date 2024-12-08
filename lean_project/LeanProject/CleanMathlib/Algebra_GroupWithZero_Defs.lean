import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.SplitIfs
assert_not_exists DenselyOrdered
universe u
variable {G₀ : Type u} {M₀ : Type*}
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0
class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  protected mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
section IsLeftCancelMulZero
variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}
theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h
theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective (a * ·) :=
  fun _ _ => mul_left_cancel₀ ha
end IsLeftCancelMulZero
class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  protected mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c
section IsRightCancelMulZero
variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}
theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h
theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b :=
  fun _ _ => mul_right_cancel₀ hb
end IsRightCancelMulZero
class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀]
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀ : Prop
export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero
class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0
export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀
class CancelMonoidWithZero (M₀ : Type*) extends MonoidWithZero M₀, IsCancelMulZero M₀
class CommMonoidWithZero (M₀ : Type*) extends CommMonoid M₀, MonoidWithZero M₀
section CancelMonoidWithZero
variable [CancelMonoidWithZero M₀] {a b c : M₀}
theorem mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  (mul_left_injective₀ hc).eq_iff
theorem mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  (mul_right_injective₀ ha).eq_iff
end CancelMonoidWithZero
section CommSemigroup
variable [CommSemigroup M₀] [Zero M₀]
lemma IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ :=
{ mul_right_cancel_of_ne_zero :=
    fun hb h => mul_left_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _)) }
lemma IsRightCancelMulZero.to_isLeftCancelMulZero [IsRightCancelMulZero M₀] :
    IsLeftCancelMulZero M₀ :=
{ mul_left_cancel_of_ne_zero :=
    fun hb h => mul_right_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _)) }
lemma IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsLeftCancelMulZero.to_isRightCancelMulZero with }
lemma IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsRightCancelMulZero.to_isLeftCancelMulZero with }
end CommSemigroup
class CancelCommMonoidWithZero (M₀ : Type*) extends CommMonoidWithZero M₀, IsLeftCancelMulZero M₀
attribute [instance 75] CancelCommMonoidWithZero.toCommMonoidWithZero
instance (priority := 100) CancelCommMonoidWithZero.toCancelMonoidWithZero
    [CancelCommMonoidWithZero M₀] : CancelMonoidWithZero M₀ :=
{ IsLeftCancelMulZero.to_isCancelMulZero (M₀ := M₀) with }
class MulDivCancelClass (M₀ : Type*) [MonoidWithZero M₀] [Div M₀] : Prop where
  protected mul_div_cancel (a b : M₀) : b ≠ 0 → a * b / b = a
section MulDivCancelClass
variable [MonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]
@[simp] lemma mul_div_cancel_right₀ (a : M₀) {b : M₀} (hb : b ≠ 0) : a * b / b = a :=
  MulDivCancelClass.mul_div_cancel _ _ hb
end MulDivCancelClass
section MulDivCancelClass
variable [CommMonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]
@[simp] lemma mul_div_cancel_left₀ (b : M₀) {a : M₀} (ha : a ≠ 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_right₀ _ ha]
end MulDivCancelClass
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  protected inv_zero : (0 : G₀)⁻¹ = 0
  protected mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1
section GroupWithZero
variable [GroupWithZero G₀] {a : G₀}
@[simp] lemma inv_zero : (0 : G₀)⁻¹ = 0 := GroupWithZero.inv_zero
@[simp] lemma mul_inv_cancel₀ (h : a ≠ 0) : a * a⁻¹ = 1 := GroupWithZero.mul_inv_cancel a h
instance (priority := 100) GroupWithZero.toMulDivCancelClass : MulDivCancelClass G₀ where
  mul_div_cancel a b hb := by rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hb, mul_one]
end GroupWithZero
class CommGroupWithZero (G₀ : Type*) extends CommMonoidWithZero G₀, GroupWithZero G₀
section
variable [CancelMonoidWithZero M₀] {x : M₀}
lemma eq_zero_or_one_of_sq_eq_self (hx : x ^ 2 = x) : x = 0 ∨ x = 1 :=
  or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)
end
section GroupWithZero
variable [GroupWithZero G₀] {a b : G₀}
@[simp]
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]
@[simp]
theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
end GroupWithZero
section MulZeroClass
variable [MulZeroClass M₀]
theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b
theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a
variable [NoZeroDivisors M₀] {a b : M₀}
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := mul_eq_zero.not.trans not_or
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| or_comm.trans mul_eq_zero.symm
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 := mul_eq_zero_comm.not
theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp
theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 := mul_self_eq_zero.not
theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 := zero_eq_mul_self.not
end MulZeroClass