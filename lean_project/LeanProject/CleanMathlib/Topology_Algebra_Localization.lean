import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Topology.Algebra.Ring.Basic
variable {R : Type*} [CommRing R] [TopologicalSpace R] {M : Submonoid R}
def Localization.ringTopology : RingTopology (Localization M) :=
  RingTopology.coinduced (Localization.monoidOf M).toFun
instance : TopologicalSpace (Localization M) :=
  Localization.ringTopology.toTopologicalSpace
instance : TopologicalRing (Localization M) :=
  Localization.ringTopology.toTopologicalRing