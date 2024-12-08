import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Order.CompleteLattice
open Function
class IsAddQuantale (α : Type*) [AddSemigroup α] [CompleteLattice α] where
  protected add_sSup_distrib (x : α) (s : Set α) : x + sSup s = ⨆ y ∈ s, x + y
  protected sSup_add_distrib (s : Set α) (y : α) : sSup s + y = ⨆ x ∈ s, x + y
@[to_additive]
class IsQuantale (α : Type*) [Semigroup α] [CompleteLattice α] where
  protected mul_sSup_distrib (x : α) (s : Set α) : x * sSup s = ⨆ y ∈ s, x * y
  protected sSup_mul_distrib (s : Set α) (y : α) : sSup s * y = ⨆ x ∈ s, x * y
section
variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}
variable [Semigroup α] [CompleteLattice α] [IsQuantale α]
@[to_additive]
theorem mul_sSup_distrib : x * sSup s = ⨆ y ∈ s, x * y := IsQuantale.mul_sSup_distrib _ _
@[to_additive]
theorem sSup_mul_distrib : sSup s * x = ⨆ y ∈ s, y * x := IsQuantale.sSup_mul_distrib _ _
end
namespace IsAddQuantale
variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}
variable [AddSemigroup α] [CompleteLattice α] [IsAddQuantale α]
def leftAddResiduation (x y : α) := sSup {z | z + x ≤ y}
def rightAddResiduation (x y : α) := sSup {z | x + z ≤ y}
@[inherit_doc]
scoped infixr:60 " ⇨ₗ " => leftAddResiduation
@[inherit_doc]
scoped infixr:60 " ⇨ᵣ " => rightAddResiduation
end IsAddQuantale
namespace IsQuantale
variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}
variable [Semigroup α] [CompleteLattice α] [IsQuantale α]
@[to_additive existing]
def leftMulResiduation (x y : α) := sSup {z | z * x ≤ y}
@[to_additive existing]
def rightMulResiduation (x y : α) := sSup {z | x * z ≤ y}
@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ₗ " => leftMulResiduation
@[inherit_doc, to_additive existing]
scoped infixr:60 " ⇨ᵣ " => rightMulResiduation
@[to_additive]
theorem mul_iSup_distrib : x * ⨆ i, f i = ⨆ i, x * f i := by
  rw [iSup, mul_sSup_distrib, iSup_range]
@[to_additive]
theorem iSup_mul_distrib : (⨆ i, f i) * x = ⨆ i, f i * x := by
  rw [iSup, sSup_mul_distrib, iSup_range]
@[to_additive]
theorem mul_sup_distrib : x * (y ⊔ z) = (x * y) ⊔ (x * z) := by
  rw [← iSup_pair, ← sSup_pair, mul_sSup_distrib]
@[to_additive]
theorem sup_mul_distrib : (x ⊔ y) * z = (x * z) ⊔ (y * z) := by
  rw [← (@iSup_pair _ _ _ (fun _? => _? * z) _ _), ← sSup_pair, sSup_mul_distrib]
@[to_additive]
instance : MulLeftMono α where
  elim := by
    intro _ _ _; simp only; intro
    rw [← left_eq_sup, ← mul_sup_distrib, sup_of_le_left]
    trivial
@[to_additive]
instance : MulRightMono α where
  elim := by
    intro _ _ _; simp only; intro
    rw [← left_eq_sup, ← sup_mul_distrib, sup_of_le_left]
    trivial
@[to_additive]
theorem leftMulResiduation_le_iff_mul_le : x ≤ y ⇨ₗ z ↔ x * y ≤ z where
  mp h1 := by
    apply le_trans (mul_le_mul_right' h1 _)
    simp_all only [leftMulResiduation, sSup_mul_distrib, Set.mem_setOf_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1
@[to_additive]
theorem rightMulResiduation_le_iff_mul_le : x ≤ y ⇨ᵣ z ↔ y * x ≤ z where
  mp h1 := by
    apply le_trans (mul_le_mul_left' h1 _)
    simp_all only [rightMulResiduation, mul_sSup_distrib, Set.mem_setOf_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1
end IsQuantale