import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Basic
open scoped TensorProduct
open Submodule
variable {R M N : Type*}
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
variable {M₁ M₂ : Submodule R M} {N₁ N₂ : Submodule R N}
namespace TensorProduct
theorem exists_multiset (x : M ⊗[R] N) :
    ∃ S : Multiset (M × N), x = (S.map fun i ↦ i.1 ⊗ₜ[R] i.2).sum := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨{(x, y)}, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    exact ⟨Sx + Sy, by rw [Multiset.map_add, Multiset.sum_add, hx, hy]⟩
theorem exists_finsupp_left (x : M ⊗[R] N) :
    ∃ S : M →₀ N, x = S.sum fun m n ↦ m ⊗ₜ[R] n := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul x y => exact ⟨Finsupp.single x y, by simp⟩
  | add x y hx hy =>
    obtain ⟨Sx, hx⟩ := hx
    obtain ⟨Sy, hy⟩ := hy
    use Sx + Sy
    rw [hx, hy]
    exact (Finsupp.sum_add_index' (by simp) TensorProduct.tmul_add).symm
theorem exists_finsupp_right (x : M ⊗[R] N) :
    ∃ S : N →₀ M, x = S.sum fun n m ↦ m ⊗ₜ[R] n := by
  obtain ⟨S, h⟩ := exists_finsupp_left (TensorProduct.comm R M N x)
  refine ⟨S, (TensorProduct.comm R M N).injective ?_⟩
  simp_rw [h, Finsupp.sum, map_sum, comm_tmul]
theorem exists_finset (x : M ⊗[R] N) :
    ∃ S : Finset (M × N), x = S.sum fun i ↦ i.1 ⊗ₜ[R] i.2 := by
  obtain ⟨S, h⟩ := exists_finsupp_left x
  use S.graph
  rw [h, Finsupp.sum]
  apply Finset.sum_nbij' (fun m ↦ ⟨m, S m⟩) Prod.fst <;> simp
theorem exists_finite_submodule_of_finite (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ (M' : Submodule R M) (N' : Submodule R N), Module.Finite R M' ∧ Module.Finite R N' ∧
      s ⊆ LinearMap.range (mapIncl M' N') := by
  simp_rw [Module.Finite.iff_fg]
  refine hs.induction_on ⟨_, _, fg_bot, fg_bot, Set.empty_subset _⟩ ?_
  rintro a s - - ⟨M', N', hM', hN', h⟩
  refine TensorProduct.induction_on a ?_ (fun x y ↦ ?_) fun x y hx hy ↦ ?_
  · exact ⟨M', N', hM', hN', Set.insert_subset (zero_mem _) h⟩
  · refine ⟨_, _, hM'.sup (fg_span_singleton x),
      hN'.sup (fg_span_singleton y), Set.insert_subset ?_ fun z hz ↦ ?_⟩
    · exact ⟨⟨x, mem_sup_right (mem_span_singleton_self x)⟩ ⊗ₜ
        ⟨y, mem_sup_right (mem_span_singleton_self y)⟩, rfl⟩
    · exact range_mapIncl_mono le_sup_left le_sup_left (h hz)
  · obtain ⟨M₁', N₁', hM₁', hN₁', h₁⟩ := hx
    obtain ⟨M₂', N₂', hM₂', hN₂', h₂⟩ := hy
    refine ⟨_, _, hM₁'.sup hM₂', hN₁'.sup hN₂', Set.insert_subset (add_mem ?_ ?_) fun z hz ↦ ?_⟩
    · exact range_mapIncl_mono le_sup_left le_sup_left (h₁ (Set.mem_insert x s))
    · exact range_mapIncl_mono le_sup_right le_sup_right (h₂ (Set.mem_insert y s))
    · exact range_mapIncl_mono le_sup_left le_sup_left (h₁ (Set.subset_insert x s hz))
theorem exists_finite_submodule_left_of_finite (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ M' : Submodule R M, Module.Finite R M' ∧ s ⊆ LinearMap.range (M'.subtype.rTensor N) := by
  obtain ⟨M', _, hfin, _, h⟩ := exists_finite_submodule_of_finite s hs
  refine ⟨M', hfin, ?_⟩
  rw [mapIncl, ← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)
theorem exists_finite_submodule_right_of_finite (s : Set (M ⊗[R] N)) (hs : s.Finite) :
    ∃ N' : Submodule R N, Module.Finite R N' ∧ s ⊆ LinearMap.range (N'.subtype.lTensor M) := by
  obtain ⟨_, N', _, hfin, h⟩ := exists_finite_submodule_of_finite s hs
  refine ⟨N', hfin, ?_⟩
  rw [mapIncl, ← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)
theorem exists_finite_submodule_of_finite' (s : Set (M₁ ⊗[R] N₁)) (hs : s.Finite) :
    ∃ (M' : Submodule R M) (N' : Submodule R N) (hM : M' ≤ M₁) (hN : N' ≤ N₁),
      Module.Finite R M' ∧ Module.Finite R N' ∧
        s ⊆ LinearMap.range (TensorProduct.map (inclusion hM) (inclusion hN)) := by
  obtain ⟨M', N', _, _, h⟩ := exists_finite_submodule_of_finite s hs
  have hM := map_subtype_le M₁ M'
  have hN := map_subtype_le N₁ N'
  refine ⟨_, _, hM, hN, .map _ _, .map _ _, ?_⟩
  rw [mapIncl,
    show M'.subtype = inclusion hM ∘ₗ M₁.subtype.submoduleMap M' by ext; simp,
    show N'.subtype = inclusion hN ∘ₗ N₁.subtype.submoduleMap N' by ext; simp,
    map_comp] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)
theorem exists_finite_submodule_left_of_finite' (s : Set (M₁ ⊗[R] N₁)) (hs : s.Finite) :
    ∃ (M' : Submodule R M) (hM : M' ≤ M₁), Module.Finite R M' ∧
      s ⊆ LinearMap.range ((inclusion hM).rTensor N₁) := by
  obtain ⟨M', _, hM, _, hfin, _, h⟩ := exists_finite_submodule_of_finite' s hs
  refine ⟨M', hM, hfin, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)
theorem exists_finite_submodule_right_of_finite' (s : Set (M₁ ⊗[R] N₁)) (hs : s.Finite) :
    ∃ (N' : Submodule R N) (hN : N' ≤ N₁), Module.Finite R N' ∧
      s ⊆ LinearMap.range ((inclusion hN).lTensor M₁) := by
  obtain ⟨_, N', _, hN, _, hfin, h⟩ := exists_finite_submodule_of_finite' s hs
  refine ⟨N', hN, hfin, ?_⟩
  rw [← LinearMap.lTensor_comp_rTensor] at h
  exact h.trans (LinearMap.range_comp_le_range _ _)
end TensorProduct