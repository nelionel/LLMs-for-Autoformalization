import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Order.MinMax
universe u
variable {α : Type u}
class ExistsAddOfLE (α : Type u) [Add α] [LE α] : Prop where
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c
@[to_additive]
class ExistsMulOfLE (α : Type u) [Mul α] [LE α] : Prop where
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a * c
export ExistsMulOfLE (exists_mul_of_le)
export ExistsAddOfLE (exists_add_of_le)
@[to_additive]
instance (priority := 100) Group.existsMulOfLE (α : Type u) [Group α] [LE α] : ExistsMulOfLE α :=
  ⟨fun {a b} _ => ⟨a⁻¹ * b, (mul_inv_cancel_left _ _).symm⟩⟩
section MulOneClass
variable [MulOneClass α] [Preorder α] [ExistsMulOfLE α] {a b : α}
@[to_additive] lemma exists_one_le_mul_of_le [MulLeftReflectLE α] (h : a ≤ b) :
    ∃ c, 1 ≤ c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h; exact ⟨c, one_le_of_le_mul_right h, rfl⟩
@[to_additive] lemma exists_one_lt_mul_of_lt' [MulLeftReflectLT α] (h : a < b) :
    ∃ c, 1 < c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le; exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩
@[to_additive] lemma le_iff_exists_one_le_mul [MulLeftMono α]
    [MulLeftReflectLE α] : a ≤ b ↔ ∃ c, 1 ≤ c ∧ a * c = b :=
  ⟨exists_one_le_mul_of_le, by rintro ⟨c, hc, rfl⟩; exact le_mul_of_one_le_right' hc⟩
@[to_additive] lemma lt_iff_exists_one_lt_mul [MulLeftStrictMono α]
    [MulLeftReflectLT α] : a < b ↔ ∃ c, 1 < c ∧ a * c = b :=
  ⟨exists_one_lt_mul_of_lt', by rintro ⟨c, hc, rfl⟩; exact lt_mul_of_one_lt_right' _ hc⟩
end MulOneClass
section ExistsMulOfLE
variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [MulLeftReflectLT α] {a b : α}
@[to_additive]
theorem le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
  le_of_forall_le_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ (one_lt_of_lt_mul_right hxb)
@[to_additive]
theorem le_of_forall_one_lt_lt_mul' (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_forall_one_lt_le_mul fun ε hε => (h ε hε).le
@[to_additive]
theorem le_iff_forall_one_lt_lt_mul' [MulLeftStrictMono α] :
    a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩
@[to_additive]
theorem le_iff_forall_one_lt_le_mul [MulLeftStrictMono α] :
    a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε :=
  ⟨fun h _ hε ↦ lt_mul_of_le_of_one_lt h hε |>.le, le_of_forall_one_lt_le_mul⟩
end ExistsMulOfLE