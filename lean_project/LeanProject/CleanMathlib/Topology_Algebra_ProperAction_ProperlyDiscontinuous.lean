import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]
open Prod Set
theorem properlyDiscontinuousSMul_iff_properSMul [T2Space X] [DiscreteTopology G]
    [ContinuousConstSMul G X] [CompactlyGeneratedSpace (X × X)] :
    ProperlyDiscontinuousSMul G X ↔ ProperSMul G X := by
  constructor
  · intro h
    rw [properSMul_iff]
    refine isProperMap_iff_isCompact_preimage.2
      ⟨(continuous_prod_mk.2
      ⟨continuous_prod_of_discrete_left.2 continuous_const_smul, by fun_prop⟩),
      fun K hK ↦ ?_⟩
    let K' := fst '' K ∪ snd '' K
    have hK' : IsCompact K' := (hK.image continuous_fst).union (hK.image continuous_snd)
    let E := {g : G | Set.Nonempty ((g • ·) '' K' ∩ K')}
    have fin : Set.Finite E := by
      simp_rw [E, nonempty_iff_ne_empty]
      exact h.finite_disjoint_inter_image hK' hK'
    have : (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (K' ×ˢ K') =
        ⋃ g ∈ E, {g} ×ˢ ((g⁻¹ • ·) '' K' ∩ K') := by
      ext gx
      simp only [mem_preimage, mem_prod, nonempty_def, mem_inter_iff, mem_image,
        exists_exists_and_eq_and, mem_setOf_eq, singleton_prod, iUnion_exists, biUnion_and',
        mem_iUnion, exists_prop, E]
      constructor
      · exact fun ⟨gx_mem, x_mem⟩ ↦ ⟨gx.2, x_mem, gx.1, gx_mem,
          ⟨gx.2, ⟨⟨gx.1 • gx.2, gx_mem, by simp⟩, x_mem⟩, rfl⟩⟩
      · rintro ⟨x, -, g, -, ⟨-, ⟨⟨x', x'_mem, rfl⟩, ginvx'_mem⟩, rfl⟩⟩
        exact ⟨by simpa, by simpa⟩
    have : IsCompact ((fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) ⁻¹' (K' ×ˢ K')) :=
      this ▸ fin.isCompact_biUnion fun g hg ↦
        isCompact_singleton.prod <| (hK'.image <| continuous_const_smul _).inter hK'
    exact this.of_isClosed_subset (hK.isClosed.preimage <|
      continuous_prod_mk.2
      ⟨continuous_prod_of_discrete_left.2 continuous_const_smul, by fun_prop⟩) <|
      preimage_mono fun x hx ↦ ⟨Or.inl ⟨x, hx, rfl⟩, Or.inr ⟨x, hx, rfl⟩⟩
  · intro h; constructor
    intro K L hK hL
    simp_rw [← nonempty_iff_ne_empty]
    apply IsCompact.finite_of_discrete
    have : IsProperMap (fun gx : G × X ↦ (gx.1⁻¹ • gx.2, gx.2)) :=
      (IsProperMap.prodMap (Homeomorph.isProperMap (Homeomorph.inv G)) isProperMap_id).comp <|
        ProperSMul.isProperMap_smul_pair
    have eq : {g | Set.Nonempty ((g • ·) '' K ∩ L)} =
        fst '' ((fun gx : G × X ↦ (gx.1⁻¹ • gx.2, gx.2)) ⁻¹' (K ×ˢ L)) := by
      simp_rw [nonempty_def]
      ext g; constructor
      · exact fun ⟨_, ⟨x, x_mem, rfl⟩, hx⟩ ↦ ⟨(g, g • x), ⟨by simpa, hx⟩, rfl⟩
      · rintro ⟨gx, hgx, rfl⟩
        exact ⟨gx.2, ⟨gx.1⁻¹ • gx.2, hgx.1, by simp⟩, hgx.2⟩
    exact eq ▸ IsCompact.image (this.isCompact_preimage <| hK.prod hL) continuous_fst