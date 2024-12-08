import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.GroupWithZero.Units.Basic
assert_not_exists Multiset
namespace GroupWithZero
variable {α : Type*} [GroupWithZero α] {a b : α}
@[simp] lemma isConj_iff₀ : IsConj a b ↔ ∃ c : α, c ≠ 0 ∧ c * a * c⁻¹ = b := by
  rw [IsConj, Units.exists_iff_ne_zero (p := (SemiconjBy · a b))]
  congr! 2 with c
  exact and_congr_right (mul_inv_eq_iff_eq_mul₀ · |>.symm)
lemma conj_pow₀ {s : ℕ} {a d : α} (ha : a ≠ 0) : (a⁻¹ * d * a) ^ s = a⁻¹ * d ^ s * a :=
  let u : αˣ := ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  Units.conj_pow' u d s
end GroupWithZero