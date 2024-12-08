import Mathlib.Algebra.Group.Defs
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered
universe u
variable {α : Type u}
class Invertible [Mul α] [One α] (a : α) : Type u where
  invOf : α
  invOf_mul_self : invOf * a = 1
  mul_invOf_self : a * invOf = 1
prefix:max "⅟" => Invertible.invOf
@[simp]
theorem invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible a} : ⅟ a * a = 1 :=
  Invertible.invOf_mul_self
theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟ a * a = 1 := invOf_mul_self' _
@[simp]
theorem mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible a} : a * ⅟ a = 1 :=
  Invertible.mul_invOf_self
theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟ a = 1 := mul_invOf_self' _
@[simp]
theorem invOf_mul_cancel_left' [Monoid α] (a b : α) {_ : Invertible a} : ⅟ a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b
theorem invOf_mul_cancel_left [Monoid α] (a b : α) [Invertible a] : ⅟ a * (a * b) = b :=
  invOf_mul_cancel_left' _ _
@[deprecated (since := "2024-09-07")] alias invOf_mul_self_assoc' := invOf_mul_cancel_left'
@[deprecated (since := "2024-09-07")] alias invOf_mul_self_assoc := invOf_mul_cancel_left
@[simp]
theorem mul_invOf_cancel_left' [Monoid α] (a b : α) {_ : Invertible a} : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b
theorem mul_invOf_cancel_left [Monoid α] (a b : α) [Invertible a] : a * (⅟ a * b) = b :=
  mul_invOf_cancel_left' a b
@[deprecated (since := "2024-09-07")] alias mul_invOf_self_assoc' := mul_invOf_cancel_left'
@[deprecated (since := "2024-09-07")] alias mul_invOf_self_assoc := mul_invOf_cancel_left
@[simp]
theorem invOf_mul_cancel_right' [Monoid α] (a b : α) {_ : Invertible b} : a * ⅟ b * b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b
theorem invOf_mul_cancel_right [Monoid α] (a b : α) [Invertible b] : a * ⅟ b * b = a :=
  invOf_mul_cancel_right' _ _
@[deprecated (since := "2024-09-07")] alias mul_invOf_mul_self_cancel' := invOf_mul_cancel_right'
@[deprecated (since := "2024-09-07")] alias mul_invOf_mul_self_cancel := invOf_mul_cancel_right
@[simp]
theorem mul_invOf_cancel_right' [Monoid α] (a b : α) {_ : Invertible b} : a * b * ⅟ b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b
theorem mul_invOf_cancel_right [Monoid α] (a b : α) [Invertible b] : a * b * ⅟ b = a :=
  mul_invOf_cancel_right' _ _
@[deprecated (since := "2024-09-07")] alias mul_mul_invOf_self_cancel' := mul_invOf_cancel_right'
@[deprecated (since := "2024-09-07")] alias mul_mul_invOf_self_cancel := mul_invOf_cancel_right
theorem invOf_eq_right_inv [Monoid α] {a b : α} [Invertible a] (hac : a * b = 1) : ⅟ a = b :=
  left_inv_eq_right_inv (invOf_mul_self _) hac
theorem invOf_eq_left_inv [Monoid α] {a b : α} [Invertible a] (hac : b * a = 1) : ⅟ a = b :=
  (left_inv_eq_right_inv hac (mul_invOf_self _)).symm
theorem invertible_unique {α : Type u} [Monoid α] (a b : α) [Invertible a] [Invertible b]
    (h : a = b) : ⅟ a = ⅟ b := by
  apply invOf_eq_right_inv
  rw [h, mul_invOf_self]
instance Invertible.subsingleton [Monoid α] (a : α) : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩
@[congr]
theorem Invertible.congr [Monoid α] (a b : α) [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b := by subst h; congr; apply Subsingleton.allEq
def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟ r) : Invertible s where
  invOf := si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]
abbrev Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl
def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel a, mul_inv_cancel a⟩
@[simp]
theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel a)
def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩
@[simp]
theorem invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟ (1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)
theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟ (1 : α) = 1 := invOf_one'
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟ a) :=
  ⟨a, mul_invOf_self a, invOf_mul_self a⟩
@[simp]
theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟ a)] : ⅟ (⅟ a) = a :=
  invOf_eq_right_inv (invOf_mul_self _)
@[simp]
theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟ a = ⅟ b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩
def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟ b * ⅟ a, by simp [← mul_assoc], by simp [← mul_assoc]⟩
@[simp]
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟ (a * b) = ⅟ b * ⅟ a :=
  invOf_eq_right_inv (by simp [← mul_assoc])
abbrev Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _
section
variable [Monoid α] {a b c : α} [Invertible c]
variable (c) in
theorem mul_left_inj_of_invertible : a * c = b * c ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩
variable (c) in
theorem mul_right_inj_of_invertible : c * a = c * b ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩
theorem invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b := by
  rw [← mul_right_inj_of_invertible (c := c), mul_invOf_cancel_left]
theorem mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b := by
  rw [← mul_right_inj_of_invertible (c := ⅟c), invOf_mul_cancel_left]
theorem mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c := by
  rw [← mul_left_inj_of_invertible (c := c), invOf_mul_cancel_right]
theorem mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c := by
  rw [← mul_left_inj_of_invertible (c := ⅟c), mul_invOf_cancel_right]
end