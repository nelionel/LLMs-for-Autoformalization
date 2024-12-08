import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
namespace Field
variable (K : Type*) [Field K]
def absoluteGaloisGroup := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K
local notation "G_K" => absoluteGaloisGroup
noncomputable instance : Group (G_K K) := AlgEquiv.aut
noncomputable instance : TopologicalSpace (G_K K) := krullTopology K (AlgebraicClosure K)
instance absoluteGaloisGroup.commutator_closure_isNormal :
    (commutator (G_K K)).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator (G_K K))
abbrev absoluteGaloisGroupAbelianization := TopologicalAbelianization (G_K K)
local notation "G_K_ab" => absoluteGaloisGroupAbelianization
end Field