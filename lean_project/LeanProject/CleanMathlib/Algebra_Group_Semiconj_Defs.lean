import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs.Unbundled
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
variable {S M G : Type*}
@[to_additive "`x` is additive semiconjugate to `y` by `a` if `a + x = y + a`"]
def SemiconjBy [Mul M] (a x y : M) : Prop :=
  a * x = y * a
namespace SemiconjBy
@[to_additive "Equality behind `AddSemiconjBy a x y`; useful for rewriting."]
protected theorem eq [Mul S] {a x y : S} (h : SemiconjBy a x y) : a * x = y * a :=
  h
section Semigroup
variable [Semigroup S] {a b x y z x' y' : S}
@[to_additive (attr := simp) "If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x + x'` to `y + y'`."]
theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by
  unfold SemiconjBy
  rw [← mul_assoc, h.eq, mul_assoc, h'.eq, ← mul_assoc]
@[to_additive "If `b` semiconjugates `x` to `y` and `a` semiconjugates `y` to `z`, then `a + b`
semiconjugates `x` to `z`."]
theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy
  rw [mul_assoc, hb.eq, ← mul_assoc, ha.eq, mul_assoc]
@[to_additive "The relation “there exists an element that semiconjugates `a` to `b`” on an additive
semigroup is transitive."]
protected theorem transitive : Transitive fun a b : S ↦ ∃ c, SemiconjBy c a b
  | _, _, _, ⟨x, hx⟩, ⟨y, hy⟩ => ⟨y * x, hy.mul_left hx⟩
end Semigroup
section MulOneClass
variable [MulOneClass M]
@[to_additive (attr := simp) "Any element semiconjugates `0` to `0`."]
theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]
@[to_additive (attr := simp) "Zero semiconjugates any element to itself."]
theorem one_left (x : M) : SemiconjBy 1 x x :=
  Eq.symm <| one_right x
@[to_additive "The relation “there exists an element that semiconjugates `a` to `b`” on an additive
monoid (or, more generally, on an `AddZeroClass` type) is reflexive."]
protected theorem reflexive : Reflexive fun a b : M ↦ ∃ c, SemiconjBy c a b
  | a => ⟨1, one_left a⟩
end MulOneClass
section Monoid
variable [Monoid M]
@[to_additive (attr := simp)]
theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact SemiconjBy.one_right _
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul_right h
end Monoid
section Group
variable [Group G]
@[to_additive "`a` semiconjugates `x` to `a + x + -a`."]
theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_cancel, mul_one]
@[to_additive (attr := simp)]
theorem conj_iff {a x y b : G} :
    SemiconjBy (b * a * b⁻¹) (b * x * b⁻¹) (b * y * b⁻¹) ↔ SemiconjBy a x y := by
  unfold SemiconjBy
  simp only [← mul_assoc, inv_mul_cancel_right]
  repeat rw [mul_assoc]
  rw [mul_left_cancel_iff, ← mul_assoc, ← mul_assoc, mul_right_cancel_iff]
end Group
end SemiconjBy
@[to_additive (attr := simp)]
theorem semiconjBy_iff_eq [CancelCommMonoid M] {a x y : M} : SemiconjBy a x y ↔ x = y :=
  ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩