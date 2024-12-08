import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Adjoin.Basic
open Module
universe u v
namespace Subalgebra
variable {R : Type u} {S : Type v} [CommRing R] [StrongRankCondition R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S) [Free R A] [Free R B]
theorem rank_sup_le_of_free : Module.rank R ↥(A ⊔ B) ≤ Module.rank R A * Module.rank R B := by
  obtain ⟨ιA, bA⟩ := Free.exists_basis (R := R) (M := A)
  obtain ⟨ιB, bB⟩ := Free.exists_basis (R := R) (M := B)
  have h := Algebra.adjoin_union_coe_submodule R (A : Set S) (B : Set S)
  rw [A.adjoin_eq_span_basis R bA, B.adjoin_eq_span_basis R bB, ← Algebra.sup_def,
    Submodule.span_mul_span] at h
  change Module.rank R ↥(toSubmodule (A ⊔ B)) ≤ _
  rw [h, ← bA.mk_eq_rank'', ← bB.mk_eq_rank'']
  refine (rank_span_le _).trans Cardinal.mk_mul_le |>.trans ?_
  gcongr <;> exact Cardinal.mk_range_le
theorem finrank_sup_le_of_free : finrank R ↥(A ⊔ B) ≤ finrank R A * finrank R B := by
  by_cases h : Module.Finite R A ∧ Module.Finite R B
  · obtain ⟨_, _⟩ := h
    simpa only [map_mul] using Cardinal.toNat_le_toNat (A.rank_sup_le_of_free B)
      (Cardinal.mul_lt_aleph0 (rank_lt_aleph0 R A) (rank_lt_aleph0 R B))
  wlog hA : ¬ Module.Finite R A generalizing A B
  · have := this B A (fun h' ↦ h h'.symm) (not_and.1 h (of_not_not hA))
    rwa [sup_comm, mul_comm] at this
  rw [← rank_lt_aleph0_iff, not_lt] at hA
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show toSubmodule A ≤ toSubmodule (A ⊔ B) by simp
  rw [show finrank R A = 0 from Cardinal.toNat_apply_of_aleph0_le hA,
    show finrank R ↥(A ⊔ B) = 0 from Cardinal.toNat_apply_of_aleph0_le (hA.trans this), zero_mul]
end Subalgebra