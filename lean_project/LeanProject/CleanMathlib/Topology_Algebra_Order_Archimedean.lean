import Mathlib.GroupTheory.Archimedean
import Mathlib.Topology.Order.Basic
open Set
theorem Rat.denseRange_cast {𝕜} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [Archimedean 𝕜] : DenseRange ((↑) : ℚ → 𝕜) :=
  dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 <| exists_rat_btwn h
namespace AddSubgroup
variable {G : Type*} [LinearOrderedAddCommGroup G] [TopologicalSpace G] [OrderTopology G]
  [Archimedean G]
theorem dense_of_not_isolated_zero (S : AddSubgroup G) (hS : ∀ ε > 0, ∃ g ∈ S, g ∈ Ioo 0 ε) :
    Dense (S : Set G) := by
  cases subsingleton_or_nontrivial G
  · refine fun x => _root_.subset_closure ?_
    rw [Subsingleton.elim x 0]
    exact zero_mem S
  refine dense_of_exists_between fun a b hlt => ?_
  rcases hS (b - a) (sub_pos.2 hlt) with ⟨g, hgS, hg0, hg⟩
  rcases (existsUnique_add_zsmul_mem_Ioc hg0 0 a).exists with ⟨m, hm⟩
  rw [zero_add] at hm
  refine ⟨m • g, zsmul_mem hgS _, hm.1, hm.2.trans_lt ?_⟩
  rwa [lt_sub_iff_add_lt'] at hg
theorem dense_of_no_min (S : AddSubgroup G) (hbot : S ≠ ⊥)
    (H : ¬∃ a : G, IsLeast { g : G | g ∈ S ∧ 0 < g } a) : Dense (S : Set G) := by
  refine S.dense_of_not_isolated_zero fun ε ε0 => ?_
  contrapose! H
  exact exists_isLeast_pos hbot ε0 (disjoint_left.2 H)
theorem dense_or_cyclic (S : AddSubgroup G) : Dense (S : Set G) ∨ ∃ a : G, S = closure {a} := by
  refine (em _).imp (dense_of_not_isolated_zero S) fun h => ?_
  push_neg at h
  rcases h with ⟨ε, ε0, hε⟩
  exact cyclic_of_isolated_zero ε0 (disjoint_left.2 hε)
end AddSubgroup