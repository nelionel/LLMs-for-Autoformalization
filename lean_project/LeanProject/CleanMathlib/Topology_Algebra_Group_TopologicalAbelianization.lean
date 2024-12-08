import Mathlib.GroupTheory.Abelianization
import Mathlib.Topology.Algebra.Group.Basic
variable (G : Type*) [Group G] [TopologicalSpace G] [TopologicalGroup G]
instance instNormalCommutatorClosure : (commutator G).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator G)
abbrev TopologicalAbelianization := G ⧸ Subgroup.topologicalClosure (commutator G)
local notation "G_ab" => TopologicalAbelianization
namespace TopologicalAbelianization
instance commGroup : CommGroup (G_ab G) where
  mul_comm := fun x y =>
    Quotient.inductionOn₂' x y fun a b =>
      Quotient.sound' <|
        QuotientGroup.leftRel_apply.mpr <| by
          have h : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by group
          rw [h]
          exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
            (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
  __ : Group (G_ab G) := inferInstance
end TopologicalAbelianization