import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend
open Filter
section Ring
variable {R : Type*}
def discrim [Ring R] (a b c : R) : R :=
  b ^ 2 - 4 * a * c
@[simp] lemma discrim_neg [Ring R] (a b c : R) : discrim (-a) (-b) (-c) = discrim a b c := by
  simp [discrim]
variable [CommRing R] {a b c : R}
lemma discrim_eq_sq_of_quadratic_eq_zero {x : R} (h : a * (x * x) + b * x + c = 0) :
    discrim a b c = (2 * a * x + b) ^ 2 := by
  rw [discrim]
  linear_combination -4 * a * h
theorem quadratic_eq_zero_iff_discrim_eq_sq [NeZero (2 : R)] [NoZeroDivisors R]
    (ha : a ≠ 0) (x : R) :
    a * (x * x) + b * x + c = 0 ↔ discrim a b c = (2 * a * x + b) ^ 2 := by
  refine ⟨discrim_eq_sq_of_quadratic_eq_zero, fun h ↦ ?_⟩
  rw [discrim] at h
  have ha : 2 * 2 * a ≠ 0 := mul_ne_zero (mul_ne_zero (NeZero.ne _) (NeZero.ne _)) ha
  apply mul_left_cancel₀ ha
  linear_combination -h
theorem quadratic_ne_zero_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s^2) (x : R) :
    a * (x * x) + b * x + c ≠ 0 :=
  mt discrim_eq_sq_of_quadratic_eq_zero (h _)
end Ring
section Field
variable {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K}
theorem quadratic_eq_zero_iff (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha, h, sq, mul_self_eq_mul_self_iff]
  field_simp
  apply or_congr
  · constructor <;> intro h' <;> linear_combination -h'
  · constructor <;> intro h' <;> linear_combination h'
theorem exists_quadratic_eq_zero (ha : a ≠ 0) (h : ∃ s, discrim a b c = s * s) :
    ∃ x, a * (x * x) + b * x + c = 0 := by
  rcases h with ⟨s, hs⟩
  use (-b + s) / (2 * a)
  rw [quadratic_eq_zero_iff ha hs]
  simp
theorem quadratic_eq_zero_iff_of_discrim_eq_zero (ha : a ≠ 0) (h : discrim a b c = 0) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = -b / (2 * a) := by
  have : discrim a b c = 0 * 0 := by rw [h, mul_zero]
  rw [quadratic_eq_zero_iff ha this, add_zero, sub_zero, or_self_iff]
end Field
section LinearOrderedField
variable {K : Type*} [LinearOrderedField K] {a b c : K}
theorem discrim_le_zero (h : ∀ x : K, 0 ≤ a * (x * x) + b * x + c) : discrim a b c ≤ 0 := by
  rw [discrim, sq]
  obtain ha | rfl | ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0
  · have : Tendsto (fun x => (a * x + b) * x + c) atTop atBot :=
      tendsto_atBot_add_const_right _ c
        ((tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop
          tendsto_id)
    rcases (this.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
    exact False.elim ((h x).not_lt <| by rwa [← mul_assoc, ← add_mul])
  · rcases eq_or_ne b 0 with (rfl | hb)
    · simp
    · have := h ((-c - 1) / b)
      rw [mul_div_cancel₀ _ hb] at this
      linarith
  · have ha' : 0 ≤ 4 * a := mul_nonneg zero_le_four ha.le
    convert neg_nonpos.2 (mul_nonneg ha' (h (-b / (2 * a)))) using 1
    field_simp
    ring
lemma discrim_le_zero_of_nonpos (h : ∀ x : K, a * (x * x) + b * x + c ≤ 0) : discrim a b c ≤ 0 :=
  discrim_neg a b c ▸ discrim_le_zero <| by simpa only [neg_mul, ← neg_add, neg_nonneg]
theorem discrim_lt_zero (ha : a ≠ 0) (h : ∀ x : K, 0 < a * (x * x) + b * x + c) :
    discrim a b c < 0 := by
  have : ∀ x : K, 0 ≤ a * (x * x) + b * x + c := fun x => le_of_lt (h x)
  refine lt_of_le_of_ne (discrim_le_zero this) fun h' ↦ ?_
  have := h (-b / (2 * a))
  have : a * (-b / (2 * a)) * (-b / (2 * a)) + b * (-b / (2 * a)) + c = 0 := by
    rw [mul_assoc, quadratic_eq_zero_iff_of_discrim_eq_zero ha h' (-b / (2 * a))]
  linarith
lemma discrim_lt_zero_of_neg (ha : a ≠ 0) (h : ∀ x : K, a * (x * x) + b * x + c < 0) :
    discrim a b c < 0 :=
  discrim_neg a b c ▸ discrim_lt_zero (neg_ne_zero.2 ha) <| by
    simpa only [neg_mul, ← neg_add, neg_pos]
end LinearOrderedField