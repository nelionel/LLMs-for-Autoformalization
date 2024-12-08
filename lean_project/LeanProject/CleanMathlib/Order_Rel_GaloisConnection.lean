import Mathlib.Data.Rel
import Mathlib.Order.GaloisConnection
variable {α β : Type*} (R : Rel α β)
namespace Rel
open OrderDual
def leftDual (J : Set α) : Set β := {b : β | ∀ ⦃a⦄, a ∈ J → R a b}
def rightDual (I : Set β) : Set α := {a : α | ∀ ⦃b⦄, b ∈ I → R a b}
theorem gc_leftDual_rightDual : GaloisConnection (toDual ∘ R.leftDual) (R.rightDual ∘ ofDual) :=
  fun _ _ ↦ ⟨fun h _ ha _ hb ↦ h (by simpa) ha, fun h _ hb _ ha ↦ h (by simpa) hb⟩
def leftFixedPoints := {J : Set α | R.rightDual (R.leftDual J) = J}
def rightFixedPoints := {I : Set β | R.leftDual (R.rightDual I) = I}
open GaloisConnection
theorem leftDual_mem_rightFixedPoint (J : Set α) : R.leftDual J ∈ R.rightFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_l; exact R.gc_leftDual_rightDual.le_u_l J
  · exact R.gc_leftDual_rightDual.l_u_le (R.leftDual J)
theorem rightDual_mem_leftFixedPoint (I : Set β) : R.rightDual I ∈ R.leftFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_u; exact R.gc_leftDual_rightDual.l_u_le I
  · exact R.gc_leftDual_rightDual.le_u_l (R.rightDual I)
def equivFixedPoints : R.leftFixedPoints ≃ R.rightFixedPoints where
  toFun := fun ⟨J, _⟩ => ⟨R.leftDual J, R.leftDual_mem_rightFixedPoint J⟩
  invFun := fun ⟨I, _⟩ => ⟨R.rightDual I, R.rightDual_mem_leftFixedPoint I⟩
  left_inv J := by cases' J with J hJ; rw [Subtype.mk.injEq, hJ]
  right_inv I := by cases' I with I hI; rw [Subtype.mk.injEq, hI]
theorem rightDual_leftDual_le_of_le {J J' : Set α} (h : J' ∈ R.leftFixedPoints) (h₁ : J ≤ J') :
    R.rightDual (R.leftDual J) ≤ J' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_u
  apply R.gc_leftDual_rightDual.monotone_l
  exact h₁
theorem leftDual_rightDual_le_of_le {I I' : Set β} (h : I' ∈ R.rightFixedPoints) (h₁ : I ≤ I') :
    R.leftDual (R.rightDual I) ≤ I' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_l
  apply R.gc_leftDual_rightDual.monotone_u
  exact h₁
end Rel