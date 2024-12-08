import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Matrix.Mul
open Finset Matrix SimpleGraph Sym2
open Matrix
namespace SimpleGraph
variable (R : Type*) {α : Type*} (G : SimpleGraph α)
noncomputable def incMatrix [Zero R] [One R] : Matrix α (Sym2 α) R := fun a =>
  (G.incidenceSet a).indicator 1
variable {R}
theorem incMatrix_apply [Zero R] [One R] {a : α} {e : Sym2 α} :
    G.incMatrix R a e = (G.incidenceSet a).indicator 1 e :=
  rfl
theorem incMatrix_apply' [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α}
    {e : Sym2 α} : G.incMatrix R a e = if e ∈ G.incidenceSet a then 1 else 0 := by
  unfold incMatrix Set.indicator
  convert rfl
section MulZeroOneClass
variable [MulZeroOneClass R] {a b : α} {e : Sym2 α}
theorem incMatrix_apply_mul_incMatrix_apply : G.incMatrix R a e * G.incMatrix R b e =
    (G.incidenceSet a ∩ G.incidenceSet b).indicator 1 e := by
  classical simp only [incMatrix, Set.indicator_apply, ite_zero_mul_ite_zero, Pi.one_apply, mul_one,
    Set.mem_inter_iff]
theorem incMatrix_apply_mul_incMatrix_apply_of_not_adj (hab : a ≠ b) (h : ¬G.Adj a b) :
    G.incMatrix R a e * G.incMatrix R b e = 0 := by
  rw [incMatrix_apply_mul_incMatrix_apply, Set.indicator_of_not_mem]
  rw [G.incidenceSet_inter_incidenceSet_of_not_adj h hab]
  exact Set.not_mem_empty e
theorem incMatrix_of_not_mem_incidenceSet (h : e ∉ G.incidenceSet a) : G.incMatrix R a e = 0 := by
  rw [incMatrix_apply, Set.indicator_of_not_mem h]
theorem incMatrix_of_mem_incidenceSet (h : e ∈ G.incidenceSet a) : G.incMatrix R a e = 1 := by
  rw [incMatrix_apply, Set.indicator_of_mem h, Pi.one_apply]
variable [Nontrivial R]
theorem incMatrix_apply_eq_zero_iff : G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a := by
  simp only [incMatrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]
theorem incMatrix_apply_eq_one_iff : G.incMatrix R a e = 1 ↔ e ∈ G.incidenceSet a := by
  unfold incMatrix Set.indicator
  simp only [Pi.one_apply]
  apply Iff.intro <;> intro h
  · split at h <;> simp_all only [zero_ne_one]
  · simp_all only [ite_true]
end MulZeroOneClass
section NonAssocSemiring
variable [NonAssocSemiring R] {a : α} {e : Sym2 α}
theorem sum_incMatrix_apply [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    ∑ e, G.incMatrix R a e = G.degree a := by
  classical simp [incMatrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset]
theorem incMatrix_mul_transpose_diag [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a a = G.degree a := by
  classical
  rw [← sum_incMatrix_apply]
  simp only [mul_apply, incMatrix_apply', transpose_apply, mul_ite, mul_one, mul_zero]
  simp_all only [ite_true, sum_boole]
theorem sum_incMatrix_apply_of_mem_edgeSet [Fintype α] :
    e ∈ G.edgeSet → ∑ a, G.incMatrix R a e = 2 := by
  classical
    refine e.ind ?_
    intro a b h
    rw [mem_edgeSet] at h
    rw [← Nat.cast_two, ← card_pair h.ne]
    simp only [incMatrix_apply', sum_boole, mk'_mem_incidenceSet_iff, h]
    congr 2
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
theorem sum_incMatrix_apply_of_not_mem_edgeSet [Fintype α] (h : e ∉ G.edgeSet) :
    ∑ a, G.incMatrix R a e = 0 :=
  sum_eq_zero fun _ _ => G.incMatrix_of_not_mem_incidenceSet fun he => h he.1
theorem incMatrix_transpose_mul_diag [Fintype α] [Decidable (e ∈ G.edgeSet)] :
    ((G.incMatrix R)ᵀ * G.incMatrix R) e e = if e ∈ G.edgeSet then 2 else 0 := by
  classical
    simp only [Matrix.mul_apply, incMatrix_apply', transpose_apply, ite_zero_mul_ite_zero, one_mul,
      sum_boole, and_self_iff]
    split_ifs with h
    · revert h
      refine e.ind ?_
      intro v w h
      rw [← Nat.cast_two, ← card_pair (G.ne_of_adj h)]
      simp only [mk'_mem_incidenceSet_iff, G.mem_edgeSet.mp h, true_and, mem_univ, forall_true_left,
        forall_eq_or_imp, forall_eq, and_self, mem_singleton, ne_eq]
      congr 2
      ext u
      simp
    · revert h
      refine e.ind ?_
      intro v w h
      simp [mk'_mem_incidenceSet_iff, G.mem_edgeSet.not.mp h]
end NonAssocSemiring
section Semiring
variable [Fintype (Sym2 α)] [Semiring R] {a b : α}
theorem incMatrix_mul_transpose_apply_of_adj (h : G.Adj a b) :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a b = (1 : R) := by
  classical
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, incMatrix_apply_mul_incMatrix_apply,
      Set.indicator_apply, Pi.one_apply, sum_boole]
    convert @Nat.cast_one R _
    convert card_singleton s(a, b)
    rw [← coe_eq_singleton, coe_filter_univ]
    exact G.incidenceSet_inter_incidenceSet_of_adj h
theorem incMatrix_mul_transpose
    [∀ a, Fintype (neighborSet G a)] [DecidableEq α] [DecidableRel G.Adj] :
    G.incMatrix R * (G.incMatrix R)ᵀ = fun a b =>
      if a = b then (G.degree a : R) else if G.Adj a b then 1 else 0 := by
  ext a b
  split_ifs with h h'
  · subst b
    exact incMatrix_mul_transpose_diag (R := R) G
  · exact G.incMatrix_mul_transpose_apply_of_adj h'
  · simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.incMatrix_apply_mul_incMatrix_apply_of_not_adj h h', sum_const_zero]
end Semiring
end SimpleGraph