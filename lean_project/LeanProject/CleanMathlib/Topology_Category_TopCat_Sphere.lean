import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Basic
universe u
namespace TopCat
noncomputable def sphere (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| (n + 1).toNat) 1
noncomputable def disk (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin <| n.toNat) 1
scoped prefix:arg "𝕊 " => sphere
scoped prefix:arg "𝔻 " => disk
end TopCat