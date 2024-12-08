import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Tactic.Abel
universe u v w
variable {α : Type u} {β : Type v} {F : Type w}
open Set Function
open Pointwise
abbrev Ideal (R : Type u) [Semiring R] :=
  Submodule R R
section Semiring
namespace Ideal
variable [Semiring α] (I : Ideal α) {a b : α}
protected theorem zero_mem : (0 : α) ∈ I :=
  Submodule.zero_mem I
protected theorem add_mem : a ∈ I → b ∈ I → a + b ∈ I :=
  Submodule.add_mem I
variable (a)
theorem mul_mem_left : b ∈ I → a * b ∈ I :=
  Submodule.smul_mem I a
variable {a}
@[ext]
theorem ext {I J : Ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  Submodule.ext h
@[simp]
theorem unit_mul_mem_iff_mem {x y : α} (hy : IsUnit y) : y * x ∈ I ↔ x ∈ I := by
  refine ⟨fun h => ?_, fun h => I.mul_mem_left y h⟩
  obtain ⟨y', hy'⟩ := hy.exists_left_inv
  have := I.mul_mem_left y' h
  rwa [← mul_assoc, hy', one_mul] at this
end Ideal
def Module.eqIdeal (R) {M} [Semiring R] [AddCommMonoid M] [Module R M] (m m' : M) : Ideal R where
  carrier := {r : R | r • m = r • m'}
  add_mem' h h' := by simpa [add_smul] using congr($h + $h')
  zero_mem' := by simp_rw [Set.mem_setOf, zero_smul]
  smul_mem' _ _ h := by simpa [mul_smul] using congr(_ • $h)
end Semiring
section CommSemiring
variable {a b : α}
namespace Ideal
variable [CommSemiring α] (I : Ideal α)
@[simp]
theorem mul_unit_mem_iff_mem {x y : α} (hy : IsUnit y) : x * y ∈ I ↔ x ∈ I :=
  mul_comm y x ▸ unit_mul_mem_iff_mem I hy
variable (b)
theorem mul_mem_right (h : a ∈ I) : a * b ∈ I :=
  mul_comm b a ▸ I.mul_mem_left b h
variable {b}
lemma mem_of_dvd (hab : a ∣ b) (ha : a ∈ I) : b ∈ I := by
  obtain ⟨c, rfl⟩ := hab; exact I.mul_mem_right _ ha
theorem pow_mem_of_mem (ha : a ∈ I) (n : ℕ) (hn : 0 < n) : a ^ n ∈ I :=
  Nat.casesOn n (Not.elim (by decide))
    (fun m _hm => (pow_succ a m).symm ▸ I.mul_mem_left (a ^ m) ha) hn
theorem pow_mem_of_pow_mem {m n : ℕ} (ha : a ^ m ∈ I) (h : m ≤ n) : a ^ n ∈ I := by
  rw [← Nat.add_sub_of_le h, pow_add]
  exact I.mul_mem_right _ ha
end Ideal
end CommSemiring
section Ring
namespace Ideal
variable [Ring α] (I : Ideal α) {a b : α}
protected theorem neg_mem_iff : -a ∈ I ↔ a ∈ I :=
  Submodule.neg_mem_iff I
protected theorem add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) :=
  Submodule.add_mem_iff_left I
protected theorem add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) :=
  Submodule.add_mem_iff_right I
protected theorem sub_mem : a ∈ I → b ∈ I → a - b ∈ I :=
  Submodule.sub_mem I
end Ideal
end Ring
section CommRing
namespace Ideal
theorem mul_sub_mul_mem {R : Type*} [CommRing R] (I : Ideal R) {a b c d : R} (h1 : a - b ∈ I)
    (h2 : c - d ∈ I) : a * c - b * d ∈ I := by
  rw [show a * c - b * d = (a - b) * c + b * (c - d) by rw [sub_mul, mul_sub]; abel]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)
end Ideal
end CommRing