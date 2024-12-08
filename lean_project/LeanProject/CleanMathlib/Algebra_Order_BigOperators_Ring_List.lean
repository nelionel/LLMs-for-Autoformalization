import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Canonical
variable {R : Type*}
@[simp] lemma CanonicallyOrderedCommSemiring.list_prod_pos
    {α : Type*} [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    ∀ {l : List α}, 0 < l.prod ↔ (∀ x ∈ l, (0 : α) < x)
  | [] => by simp
  | (x :: xs) => by simp_rw [List.prod_cons, List.forall_mem_cons,
      CanonicallyOrderedCommSemiring.mul_pos, list_prod_pos]