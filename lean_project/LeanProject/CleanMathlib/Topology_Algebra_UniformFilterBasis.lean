import Mathlib.Topology.Algebra.FilterBasis
open uniformity Filter
open Filter
namespace AddGroupFilterBasis
variable {G : Type*} [AddCommGroup G] (B : AddGroupFilterBasis G)
protected def uniformSpace : UniformSpace G :=
  @TopologicalAddGroup.toUniformSpace G _ B.topology B.isTopologicalAddGroup
protected theorem uniformAddGroup : @UniformAddGroup G B.uniformSpace _ :=
  @comm_topologicalAddGroup_is_uniform G _ B.topology B.isTopologicalAddGroup
theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.uniformSpace F ↔
      F.NeBot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ U := by
  letI := B.uniformSpace
  haveI := B.uniformAddGroup
  suffices F ×ˢ F ≤ uniformity G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine ⟨h', ?_⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change Tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_hasBasis, @forall_swap (_ ∈ _) G]
end AddGroupFilterBasis