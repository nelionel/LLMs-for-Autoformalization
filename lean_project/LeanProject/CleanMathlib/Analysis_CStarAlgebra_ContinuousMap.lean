import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
variable {α A : Type*}
noncomputable section
namespace BoundedContinuousFunction
variable [TopologicalSpace α]
instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra (α →ᵇ A) where
instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra (α →ᵇ A) where
  mul_comm := mul_comm
instance [CStarAlgebra A] : CStarAlgebra (α →ᵇ A) where
instance [CommCStarAlgebra A] : CommCStarAlgebra (α →ᵇ A) where
  mul_comm := mul_comm
end BoundedContinuousFunction
namespace ContinuousMap
variable [TopologicalSpace α] [CompactSpace α]
instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C(α, A) where
instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra C(α, A) where
  mul_comm := mul_comm
instance [CStarAlgebra A] : CStarAlgebra C(α, A) where
instance [CommCStarAlgebra A] : CommCStarAlgebra C(α, A) where
  mul_comm := mul_comm
end ContinuousMap
namespace ZeroAtInftyContinuousMap
open ZeroAtInfty
instance [TopologicalSpace α] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C₀(α, A) where
instance [TopologicalSpace α] [NonUnitalCommCStarAlgebra A] :
    NonUnitalCommCStarAlgebra C₀(α, A) where
  mul_comm := mul_comm
end ZeroAtInftyContinuousMap