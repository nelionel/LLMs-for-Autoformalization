import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.LocalExtr
open Filter Set
open Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Preorder Y]
  [OrderClosedTopology Y] {f : X → Y} {s : Set X} {a : X}
protected theorem IsMaxOn.closure (h : IsMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMaxOn f (closure s) a := fun x hx =>
  ContinuousWithinAt.closure_le hx ((hc x hx).mono subset_closure) continuousWithinAt_const h
protected theorem IsMinOn.closure (h : IsMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMinOn f (closure s) a :=
  h.dual.closure hc
protected theorem IsExtrOn.closure (h : IsExtrOn f s a) (hc : ContinuousOn f (closure s)) :
    IsExtrOn f (closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc
protected theorem IsLocalMaxOn.closure (h : IsLocalMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMaxOn f (closure s) a := by
  rcases mem_nhdsWithin.1 h with ⟨U, Uo, aU, hU⟩
  refine mem_nhdsWithin.2 ⟨U, Uo, aU, ?_⟩
  rintro x ⟨hxU, hxs⟩
  refine ContinuousWithinAt.closure_le ?_ ?_ continuousWithinAt_const hU
  · rwa [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem, ←
      mem_closure_iff_nhdsWithin_neBot]
    exact nhdsWithin_le_nhds (Uo.mem_nhds hxU)
  · exact (hc _ hxs).mono (inter_subset_right.trans subset_closure)
protected theorem IsLocalMinOn.closure (h : IsLocalMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMinOn f (closure s) a :=
  IsLocalMaxOn.closure h.dual hc
protected theorem IsLocalExtrOn.closure (h : IsLocalExtrOn f s a)
    (hc : ContinuousOn f (closure s)) : IsLocalExtrOn f (closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc