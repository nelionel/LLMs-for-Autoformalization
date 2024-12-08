import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Maps.Proper.Basic
open Set Filter
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [T2Space Y] [CompactlyGeneratedSpace Y]
variable {f : X → Y}
theorem isProperMap_iff_isCompact_preimage :
    IsProperMap f ↔ Continuous f ∧ ∀ ⦃K⦄, IsCompact K → IsCompact (f ⁻¹' K) where
  mp hf := ⟨hf.continuous, fun _ ↦ hf.isCompact_preimage⟩
  mpr := fun ⟨hf, h⟩ ↦ isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, fun _ hs ↦ CompactlyGeneratedSpace.isClosed
      fun _ hK ↦ image_inter_preimage .. ▸ (((h hK).inter_left hs).image hf).isClosed,
      fun _ ↦ h isCompact_singleton⟩
lemma isProperMap_iff_tendsto_cocompact :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) := by
  simp_rw [isProperMap_iff_isCompact_preimage,
    hasBasis_cocompact.tendsto_right_iff, ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont ↦
    ⟨fun H K hK ↦ (H hK).compl_mem_cocompact, fun H K hK ↦ ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK'y⟩
  exact hK'.of_isClosed_subset (hK.isClosed.preimage f_cont)
    (compl_le_compl_iff_le.mp hK'y)