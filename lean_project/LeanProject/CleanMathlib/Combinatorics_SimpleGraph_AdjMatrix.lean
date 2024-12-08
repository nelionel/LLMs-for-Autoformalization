import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
open Matrix
open Finset Matrix SimpleGraph
variable {V α : Type*}
namespace Matrix
structure IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where
  zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1 := by aesop
  symm : A.IsSymm := by aesop
  apply_diag : ∀ i, A i i = 0 := by aesop
namespace IsAdjMatrix
variable {A : Matrix V V α}
@[simp]
theorem apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V) :
    ¬A i i = 1 := by simp [h.apply_diag i]
@[simp]
theorem apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 1 ↔ A i j = 0 := by obtain h | h := h.zero_or_one i j <;> simp [h]
@[simp]
theorem apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 0 ↔ A i j = 1 := by rw [← apply_ne_one_iff h, Classical.not_not]
@[simps]
def toGraph [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGraph V where
  Adj i j := A i j = 1
  symm i j hij := by simp only; rwa [h.symm.apply i j]
  loopless i := by simp [h]
instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (h : IsAdjMatrix A) :
    DecidableRel h.toGraph.Adj := by
  simp only [toGraph]
  infer_instance
end IsAdjMatrix
def compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α :=
  fun i j => ite (i = j) 0 (ite (A i j = 0) 1 0)
section Compl
variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)
@[simp]
theorem compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0 := by simp [compl]
@[simp]
theorem compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 := by
  unfold compl
  split_ifs <;> simp
@[simp]
theorem isSymm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm := by
  ext
  simp [compl, h.apply, eq_comm]
@[simp]
theorem isAdjMatrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl :=
  { symm := by simp [h] }
namespace IsAdjMatrix
variable {A}
@[simp]
theorem compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl :=
  isAdjMatrix_compl A h.symm
theorem toGraph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) :
    h.compl.toGraph = h.toGraphᶜ := by
  ext v w
  cases' h.zero_or_one v w with h h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]
end IsAdjMatrix
end Compl
end Matrix
open Matrix
namespace SimpleGraph
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (α)
def adjMatrix [Zero α] [One α] : Matrix V V α :=
  of fun i j => if G.Adj i j then (1 : α) else 0
variable {α}
@[simp]
theorem adjMatrix_apply (v w : V) [Zero α] [One α] :
    G.adjMatrix α v w = if G.Adj v w then 1 else 0 :=
  rfl
@[simp]
theorem transpose_adjMatrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α := by
  ext
  simp [adj_comm]
@[simp]
theorem isSymm_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsSymm :=
  transpose_adjMatrix G
variable (α)
@[simp]
theorem isAdjMatrix_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix :=
  { zero_or_one := fun i j => by by_cases h : G.Adj i j <;> simp [h] }
theorem toGraph_adjMatrix_eq [MulZeroOneClass α] [Nontrivial α] :
    (G.isAdjMatrix_adjMatrix α).toGraph = G := by
  ext
  simp only [IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not
variable {α}
theorem one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes [DecidableEq V] [DecidableEq α]
    [NonAssocSemiring α] : 1 + G.adjMatrix α + (G.adjMatrix α).compl = Matrix.of fun _ _ ↦ 1 := by
  ext i j
  unfold Matrix.compl
  rw [of_apply, add_apply, adjMatrix_apply, add_apply, adjMatrix_apply, one_apply]
  by_cases h : G.Adj i j
  · aesop
  · split_ifs <;> simp_all
variable [Fintype V]
@[simp]
theorem adjMatrix_dotProduct [NonAssocSemiring α] (v : V) (vec : V → α) :
    dotProduct (G.adjMatrix α v) vec = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]
@[simp]
theorem dotProduct_adjMatrix [NonAssocSemiring α] (v : V) (vec : V → α) :
    dotProduct vec (G.adjMatrix α v) = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter, Finset.sum_apply]
@[simp]
theorem adjMatrix_mulVec_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (G.adjMatrix α *ᵥ vec) v = ∑ u ∈ G.neighborFinset v, vec u := by
  rw [mulVec, adjMatrix_dotProduct]
@[simp]
theorem adjMatrix_vecMul_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (vec ᵥ* G.adjMatrix α) v = ∑ u ∈ G.neighborFinset v, vec u := by
  simp only [← dotProduct_adjMatrix, vecMul]
  refine congr rfl ?_; ext x
  rw [← transpose_apply (adjMatrix α G) x v, transpose_adjMatrix]
@[simp]
theorem adjMatrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (G.adjMatrix α * M) v w = ∑ u ∈ G.neighborFinset v, M u w := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter]
@[simp]
theorem mul_adjMatrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (M * G.adjMatrix α) v w = ∑ u ∈ G.neighborFinset w, M v u := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter, adj_comm]
variable (α)
@[simp]
theorem trace_adjMatrix [AddCommMonoid α] [One α] : Matrix.trace (G.adjMatrix α) = 0 := by
  simp [Matrix.trace]
variable {α}
theorem adjMatrix_mul_self_apply_self [NonAssocSemiring α] (i : V) :
    (G.adjMatrix α * G.adjMatrix α) i i = degree G i := by simp [filter_true_of_mem]
variable {G}
theorem adjMatrix_mulVec_const_apply [NonAssocSemiring α] {a : α} {v : V} :
    (G.adjMatrix α *ᵥ Function.const _ a) v = G.degree v * a := by simp
theorem adjMatrix_mulVec_const_apply_of_regular [NonAssocSemiring α] {d : ℕ} {a : α}
    (hd : G.IsRegularOfDegree d) {v : V} : (G.adjMatrix α *ᵥ Function.const _ a) v = d * a := by
  simp [hd v]
theorem adjMatrix_pow_apply_eq_card_walk [DecidableEq V] [Semiring α] (n : ℕ) (u v : V) :
    (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n } := by
  rw [card_set_walk_length_eq]
  induction' n with n ih generalizing u v
  · obtain rfl | h := eq_or_ne u v <;> simp [finsetWalkLength, *]
  · simp only [pow_succ', finsetWalkLength, ih, adjMatrix_mul_apply]
    rw [Finset.card_biUnion]
    · norm_cast
      simp only [Nat.cast_sum, card_map, neighborFinset_def]
      apply Finset.sum_toFinset_eq_subtype
    · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
      rw [disjoint_iff_inf_le]
      intro p hp
      simp only [inf_eq_inter, mem_inter, mem_map, Function.Embedding.coeFn_mk, exists_prop] at hp
      obtain ⟨⟨px, _, rfl⟩, ⟨py, hpy, hp⟩⟩ := hp
      cases hp
      simp at hxy
theorem dotProduct_mulVec_adjMatrix [NonAssocSemiring α] (x y : V → α) :
    x ⬝ᵥ (G.adjMatrix α).mulVec y = ∑ i : V, ∑ j : V, if G.Adj i j then x i * y j else 0 := by
  simp only [dotProduct, mulVec, adjMatrix_apply, ite_mul, one_mul, zero_mul, mul_sum, mul_ite,
    mul_zero]
end SimpleGraph
namespace Matrix.IsAdjMatrix
variable [MulZeroOneClass α] [Nontrivial α]
variable {A : Matrix V V α} (h : IsAdjMatrix A)
theorem adjMatrix_toGraph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A := by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [h']
end Matrix.IsAdjMatrix