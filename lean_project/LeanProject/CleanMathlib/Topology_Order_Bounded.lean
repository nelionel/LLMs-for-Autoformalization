import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real
open Set Filter
section Real
@[deprecated isBoundedUnder_of (since := "2024-06-07")]
lemma Filter.isBounded_le_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  obtain ⟨c, hc⟩ := h.bddAbove
  exact isBoundedUnder_of ⟨c, by simpa [mem_upperBounds] using hc⟩
@[deprecated isBoundedUnder_of (since := "2024-06-07")]
lemma Filter.isBounded_ge_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  obtain ⟨c, hc⟩ := h.bddBelow
  apply isBoundedUnder_of ⟨c, by simpa [mem_lowerBounds] using hc⟩
end Real