import Mathlib.Topology.GDelta.Basic
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.UniformSpace.Basic
noncomputable section
open Topology TopologicalSpace Filter Encodable Set
open scoped Uniformity
variable {X Y : Type*}
section IsGδ
theorem IsClosed.isGδ {X : Type*} [UniformSpace X] [IsCountablyGenerated (𝓤 X)] {s : Set X}
    (hs : IsClosed s) : IsGδ s := by
  rcases (@uniformity_hasBasis_open X _).exists_antitone_subbasis with ⟨U, hUo, hU, -⟩
  rw [← hs.closure_eq, ← hU.biInter_biUnion_ball]
  refine .biInter (to_countable _) fun n _ => IsOpen.isGδ ?_
  exact isOpen_biUnion fun x _ => UniformSpace.isOpen_ball _ (hUo _).2
end IsGδ
section ContinuousAt
variable [TopologicalSpace X]
theorem IsGδ.setOf_continuousAt [UniformSpace Y] [IsCountablyGenerated (𝓤 Y)] (f : X → Y) :
    IsGδ { x | ContinuousAt f x } := by
  obtain ⟨U, _, hU⟩ := (@uniformity_hasBasis_open_symmetric Y _).exists_antitone_subbasis
  simp only [Uniform.continuousAt_iff_prod, nhds_prod_eq]
  simp only [(nhds_basis_opens _).prod_self.tendsto_iff hU.toHasBasis, forall_prop_of_true,
    setOf_forall, id]
  refine .iInter fun k ↦ IsOpen.isGδ <| isOpen_iff_mem_nhds.2 fun x ↦ ?_
  rintro ⟨s, ⟨hsx, hso⟩, hsU⟩
  filter_upwards [IsOpen.mem_nhds hso hsx] with _ hy using ⟨s, ⟨hy, hso⟩, hsU⟩
@[deprecated (since := "2024-02-15")] alias isGδ_setOf_continuousAt := IsGδ.setOf_continuousAt
end ContinuousAt