import Mathlib.Algebra.Group.Semiconj.Defs
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
variable {G M S : Type*}
@[to_additive "Two elements additively commute if `a + b = b + a`"]
def Commute [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b
@[to_additive]
theorem commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b = b * a := Iff.rfl
namespace Commute
section Mul
variable [Mul S]
@[to_additive "Equality behind `AddCommute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h
@[to_additive (attr := refl, simp) "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)
@[to_additive (attr := symm) "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h
@[to_additive]
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h
@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩
@[to_additive]
instance : IsRefl S Commute :=
  ⟨Commute.refl⟩
@[to_additive]
instance on_isRefl {f : G → S} : IsRefl G fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩
end Mul
section Semigroup
variable [Semigroup S] {a b c : S}
@[to_additive (attr := simp)
"If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  SemiconjBy.mul_right hab hac
@[to_additive (attr := simp)
"If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  SemiconjBy.mul_left hac hbc
@[to_additive]
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [mul_assoc, h.eq]
@[to_additive]
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [← mul_assoc, h.eq]
@[to_additive]
protected theorem mul_mul_mul_comm (hbc : Commute b c) (a d : S) :
    a * b * (c * d) = a * c * (b * d) := by simp only [hbc.left_comm, mul_assoc]
end Semigroup
@[to_additive]
protected theorem all [CommMagma S] (a b : S) : Commute a b :=
  mul_comm a b
section MulOneClass
variable [MulOneClass M]
@[to_additive (attr := simp)]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a
@[to_additive (attr := simp)]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a
end MulOneClass
section Monoid
variable [Monoid M] {a b : M}
@[to_additive (attr := simp)]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  SemiconjBy.pow_right h n
@[to_additive (attr := simp)]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm
@[to_additive (attr := simp)]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n
@[to_additive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n
@[to_additive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n
@[to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n
@[to_additive] lemma mul_pow (h : Commute a b) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by simp only [pow_succ', h.mul_pow n, ← mul_assoc, (h.pow_left n).right_comm]
end Monoid
section DivisionMonoid
variable [DivisionMonoid G] {a b : G}
@[to_additive]
protected theorem mul_inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]
@[to_additive]
protected theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]
@[to_additive AddCommute.zsmul_add]
protected lemma mul_zpow (h : Commute a b) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ)    => by simp [zpow_natCast, h.mul_pow n]
  | .negSucc n => by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]
end DivisionMonoid
section Group
variable [Group G] {a b : G}
@[to_additive]
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]
@[to_additive]
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h.mul_inv_cancel]
end Group
end Commute