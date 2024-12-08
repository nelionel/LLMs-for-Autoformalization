import Mathlib.Topology.Order
import Mathlib.Data.ZMod.Defs
namespace ZMod
variable {N : ℕ}
instance : TopologicalSpace (ZMod N) := ⊥
instance : DiscreteTopology (ZMod N) := ⟨rfl⟩
end ZMod