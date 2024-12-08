import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Order.Ring.Defs
variable {R : Type*} [Mul R]
@[mk_iff]
inductive IsSumSq [Add R] [Zero R] : R → Prop
  | zero                              : IsSumSq 0
  | sq_add (a S : R) (pS : IsSumSq S) : IsSumSq (a * a + S)
@[deprecated (since := "2024-08-09")] alias isSumSq := IsSumSq
theorem IsSumSq.add [AddMonoid R] {S1 S2 : R} (p1 : IsSumSq S1)
    (p2 : IsSumSq S2) : IsSumSq (S1 + S2) := by
  induction p1 with
  | zero             => rw [zero_add]; exact p2
  | sq_add a S pS ih => rw [add_assoc]; exact IsSumSq.sq_add a (S + S2) ih
@[deprecated (since := "2024-08-09")] alias isSumSq.add := IsSumSq.add
theorem isSumSq_sum_mul_self {ι : Type*} [AddCommMonoid R] (s : Finset ι) (f : ι → R) :
    IsSumSq (∑ i ∈ s, f i * f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simpa only [Finset.sum_empty] using IsSumSq.zero
  | cons i s his h =>
    exact (Finset.sum_cons (β := R) his) ▸ IsSumSq.sq_add (f i) (∑ i ∈ s, f i * f i) h
variable (R) in
def sumSqIn [AddMonoid R] : AddSubmonoid R where
  carrier   := {S : R | IsSumSq S}
  zero_mem' := IsSumSq.zero
  add_mem'  := IsSumSq.add
@[deprecated (since := "2024-08-09")] alias SumSqIn := sumSqIn
theorem mem_sumSqIn_of_isSquare [AddMonoid R] {x : R} (px : IsSquare x) : x ∈ sumSqIn R := by
  rcases px with ⟨y, py⟩
  rw [py, ← AddMonoid.add_zero (y * y)]
  exact IsSumSq.sq_add _ _ IsSumSq.zero
@[deprecated (since := "2024-08-09")] alias SquaresInSumSq := mem_sumSqIn_of_isSquare
theorem AddSubmonoid.closure_isSquare [AddMonoid R] : closure {x : R | IsSquare x} = sumSqIn R := by
  refine le_antisymm (closure_le.2 (fun x hx ↦ mem_sumSqIn_of_isSquare hx)) (fun x hx ↦ ?_)
  induction hx with
  | zero             => exact zero_mem _
  | sq_add a S _ ih  => exact AddSubmonoid.add_mem _ (subset_closure ⟨a, rfl⟩) ih
@[deprecated (since := "2024-08-09")] alias SquaresAddClosure := AddSubmonoid.closure_isSquare
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R}
    (pS : IsSumSq S) : 0 ≤ S := by
  induction pS with
  | zero             => simp only [le_refl]
  | sq_add x S _ ih  => apply add_nonneg ?_ ih; simp only [← pow_two x, sq_nonneg]
@[deprecated (since := "2024-08-09")] alias isSumSq.nonneg := IsSumSq.nonneg