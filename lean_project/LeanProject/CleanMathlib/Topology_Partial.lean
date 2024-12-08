import Mathlib.Order.Filter.Partial
import Mathlib.Topology.Basic
open Filter
open Topology
variable {X Y : Type*} [TopologicalSpace X]
theorem rtendsto_nhds {r : Rel Y X} {l : Filter Y} {x : X} :
    RTendsto r l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → r.core s ∈ l :=
  all_mem_nhds_filter _ _ (fun _s _t => id) _
theorem rtendsto'_nhds {r : Rel Y X} {l : Filter Y} {x : X} :
    RTendsto' r l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → r.preimage s ∈ l := by
  rw [rtendsto'_def]
  apply all_mem_nhds_filter
  apply Rel.preimage_mono
theorem ptendsto_nhds {f : Y →. X} {l : Filter Y} {x : X} :
    PTendsto f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f.core s ∈ l :=
  rtendsto_nhds
theorem ptendsto'_nhds {f : Y →. X} {l : Filter Y} {x : X} :
    PTendsto' f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f.preimage s ∈ l :=
  rtendsto'_nhds
variable [TopologicalSpace Y]
def PContinuous (f : X →. Y) :=
  ∀ s, IsOpen s → IsOpen (f.preimage s)
theorem open_dom_of_pcontinuous {f : X →. Y} (h : PContinuous f) : IsOpen f.Dom := by
  rw [← PFun.preimage_univ]; exact h _ isOpen_univ
theorem pcontinuous_iff' {f : X →. Y} :
    PContinuous f ↔ ∀ {x y} (_ : y ∈ f x), PTendsto' f (𝓝 x) (𝓝 y) := by
  constructor
  · intro h x y h'
    simp only [ptendsto'_def, mem_nhds_iff]
    rintro s ⟨t, tsubs, opent, yt⟩
    exact ⟨f.preimage t, PFun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  intro hf s os
  rw [isOpen_iff_nhds]
  rintro x ⟨y, ys, fxy⟩ t
  rw [mem_principal]
  intro (h : f.preimage s ⊆ t)
  change t ∈ 𝓝 x
  apply mem_of_superset _ h
  have h' : ∀ s ∈ 𝓝 y, f.preimage s ∈ 𝓝 x := by
    intro s hs
    have : PTendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  show f.preimage s ∈ 𝓝 x
  apply h'
  rw [mem_nhds_iff]
  exact ⟨s, Set.Subset.refl _, os, ys⟩
theorem continuousWithinAt_iff_ptendsto_res (f : X → Y) {x : X} {s : Set X} :
    ContinuousWithinAt f s x ↔ PTendsto (PFun.res f s) (𝓝 x) (𝓝 (f x)) :=
  tendsto_iff_ptendsto _ _ _ _