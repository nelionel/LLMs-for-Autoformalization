import Mathlib.Combinatorics.SimpleGraph.Coloring
universe u v
namespace SimpleGraph
variable {V : Type u} (G : SimpleGraph V)
structure Partition where
  parts : Set (Set V)
  isPartition : Setoid.IsPartition parts
  independent : ∀ s ∈ parts, IsAntichain G.Adj s
def Partition.PartsCardLe {G : SimpleGraph V} (P : G.Partition) (n : ℕ) : Prop :=
  ∃ h : P.parts.Finite, h.toFinset.card ≤ n
def Partitionable (n : ℕ) : Prop := ∃ P : G.Partition, P.PartsCardLe n
namespace Partition
variable {G}
variable (P : G.Partition)
def partOfVertex (v : V) : Set V := Classical.choose (P.isPartition.2 v)
theorem partOfVertex_mem (v : V) : P.partOfVertex v ∈ P.parts := by
  obtain ⟨h, -⟩ := (P.isPartition.2 v).choose_spec.1
  exact h
theorem mem_partOfVertex (v : V) : v ∈ P.partOfVertex v := by
  obtain ⟨⟨_, h⟩, _⟩ := (P.isPartition.2 v).choose_spec
  exact h
theorem partOfVertex_ne_of_adj {v w : V} (h : G.Adj v w) : P.partOfVertex v ≠ P.partOfVertex w := by
  intro hn
  have hw := P.mem_partOfVertex w
  rw [← hn] at hw
  exact P.independent _ (P.partOfVertex_mem v) (P.mem_partOfVertex v) hw (G.ne_of_adj h) h
def toColoring : G.Coloring P.parts :=
  Coloring.mk (fun v ↦ ⟨P.partOfVertex v, P.partOfVertex_mem v⟩) fun hvw ↦ by
    rw [Ne, Subtype.mk_eq_mk]
    exact P.partOfVertex_ne_of_adj hvw
def toColoring' : G.Coloring (Set V) :=
  Coloring.mk P.partOfVertex fun hvw ↦ P.partOfVertex_ne_of_adj hvw
theorem colorable [Fintype P.parts] : G.Colorable (Fintype.card P.parts) :=
  P.toColoring.colorable
end Partition
variable {G}
@[simps]
def Coloring.toPartition {α : Type v} (C : G.Coloring α) : G.Partition where
  parts := C.colorClasses
  isPartition := C.colorClasses_isPartition
  independent := by
    rintro s ⟨c, rfl⟩
    apply C.color_classes_independent
@[simps]
instance : Inhabited (Partition G) := ⟨G.selfColoring.toPartition⟩
theorem partitionable_iff_colorable {n : ℕ} : G.Partitionable n ↔ G.Colorable n := by
  constructor
  · rintro ⟨P, hf, hc⟩
    have : Fintype P.parts := hf.fintype
    rw [Set.Finite.card_toFinset hf] at hc
    apply P.colorable.mono hc
  · rintro ⟨C⟩
    refine ⟨C.toPartition, C.colorClasses_finite, le_trans ?_ (Fintype.card_fin n).le⟩
    generalize_proofs h
    change Set.Finite (Coloring.colorClasses C) at h
    have : Fintype C.colorClasses := C.colorClasses_finite.fintype
    rw [h.card_toFinset]
    exact C.card_colorClasses_le
end SimpleGraph