import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.List
@[simp]
lemma CanonicallyOrderedCommSemiring.multiset_prod_pos {R : Type*}
    [CanonicallyOrderedCommSemiring R] [Nontrivial R] {m : Multiset R} :
    0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedCommSemiring.list_prod_pos