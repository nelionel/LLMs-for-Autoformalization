import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.UniformRing
open UniformSpace UniformSpace.Completion AddSubgroup OpenAddSubgroup Topology
instance {G : Type*} [AddGroup G] [UniformSpace G] [UniformAddGroup G] [NonarchimedeanAddGroup G] :
    NonarchimedeanAddGroup (Completion G) where
  is_nonarchimedean := by
    intro U hU
    obtain ⟨C, ⟨hC, C_closed⟩, C_subset_U⟩ := (closed_nhds_basis 0).mem_iff.mp hU
    have : toCompl ⁻¹' C ∈ 𝓝 0 :=
      continuous_toCompl.continuousAt.preimage_mem_nhds (by rwa [map_zero])
    obtain ⟨W, hCW⟩ := NonarchimedeanAddGroup.is_nonarchimedean (toCompl ⁻¹' C) this
    let V : Set (Completion G) := (W.map toCompl).topologicalClosure
    have : IsOpen V := by
      apply isOpen_of_mem_nhds (g := 0)
      apply (isDenseInducing_toCompl _).closure_image_mem_nhds
      exact mem_nhds_zero W
    use ⟨_, this⟩
    suffices V ⊆ C from this.trans C_subset_U
    exact closure_minimal (Set.image_subset_iff.mpr hCW) C_closed
instance {R : Type*} [Ring R] [UniformSpace R] [TopologicalRing R] [UniformAddGroup R]
    [NonarchimedeanRing R] :
    NonarchimedeanRing (Completion R) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean