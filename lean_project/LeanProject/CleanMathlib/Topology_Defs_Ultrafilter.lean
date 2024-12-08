import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Defs.Filter
variable {X : Type*} [TopologicalSpace X]
open Filter
noncomputable nonrec def Ultrafilter.lim (F : Ultrafilter X) : X :=
  @lim X _ (nonempty_of_neBot F) F