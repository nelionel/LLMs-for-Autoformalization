import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Probability.Process.Filtration
open MeasureTheory MeasurableSpace
namespace ProbabilityTheory
section MemPartition
variable {α : Type*} [m : MeasurableSpace α] {t : ℕ → Set α}
def partitionFiltration (ht : ∀ n, MeasurableSet (t n)) :
    Filtration ℕ m where
  seq n := generateFrom (memPartition t n)
  mono' := monotone_nat_of_le_succ (generateFrom_memPartition_le_succ _)
  le' := generateFrom_memPartition_le ht
lemma measurableSet_partitionFiltration_of_mem (ht : ∀ n, MeasurableSet (t n)) (n : ℕ) {s : Set α}
    (hs : s ∈ memPartition t n) :
    MeasurableSet[partitionFiltration ht n] s :=
  measurableSet_generateFrom hs
lemma measurableSet_partitionFiltration_memPartitionSet (ht : ∀ n, MeasurableSet (t n))
    (n : ℕ) (a : α) :
    MeasurableSet[partitionFiltration ht n] (memPartitionSet t n a) :=
  measurableSet_partitionFiltration_of_mem ht n (memPartitionSet_mem t n a)
lemma measurable_memPartitionSet_subtype (ht : ∀ n, MeasurableSet (t n)) (n : ℕ)
    (m : MeasurableSpace (memPartition t n)) :
    @Measurable α (memPartition t n) (partitionFiltration ht n) m
      (fun a ↦ ⟨memPartitionSet t n a, memPartitionSet_mem t n a⟩) := by
  refine @measurable_to_countable' (memPartition t n) α m _
    (partitionFiltration ht n) _ (fun s ↦ ?_)
  rcases s with ⟨s, hs⟩
  suffices MeasurableSet[partitionFiltration ht n] {x | memPartitionSet t n x = s} by
    convert this
    ext x
    simp
  simp_rw [memPartitionSet_eq_iff _ hs]
  exact measurableSet_partitionFiltration_of_mem _ _ hs
lemma measurable_partitionFiltration_memPartitionSet (ht : ∀ n, MeasurableSet (t n)) (n : ℕ) :
    Measurable[partitionFiltration ht n] (memPartitionSet t n) :=
  measurable_subtype_coe.comp (measurable_memPartitionSet_subtype ht _ _)
lemma measurable_memPartitionSet (ht : ∀ n, MeasurableSet (t n)) (n : ℕ) :
    Measurable (memPartitionSet t n) :=
  (measurable_partitionFiltration_memPartitionSet ht n).mono ((partitionFiltration ht).le n) le_rfl
lemma iSup_partitionFiltration_eq_generateFrom_range (ht : ∀ n, MeasurableSet (t n)) :
    ⨆ n, partitionFiltration ht n = generateFrom (Set.range t) := by
  conv_rhs => rw [← generateFrom_iUnion_memPartition t, ← iSup_generateFrom]
  rfl
lemma iSup_partitionFiltration (ht : ∀ n, MeasurableSet (t n))
    (ht_range : generateFrom (Set.range t) = m) :
    ⨆ n, partitionFiltration ht n = m := by
  rw [iSup_partitionFiltration_eq_generateFrom_range ht, ht_range]
end MemPartition
section CountableFiltration
variable {α : Type*} [MeasurableSpace α] [CountablyGenerated α]
def countableFiltration (α : Type*) [m : MeasurableSpace α] [CountablyGenerated α] :
    Filtration ℕ m where
  seq n := generateFrom (countablePartition α n)
  mono' := monotone_nat_of_le_succ (generateFrom_countablePartition_le_succ _)
  le' := generateFrom_countablePartition_le α
lemma measurableSet_countableFiltration_of_mem (n : ℕ) {s : Set α}
    (hs : s ∈ countablePartition α n) :
    MeasurableSet[countableFiltration α n] s :=
  measurableSet_generateFrom hs
lemma measurableSet_countableFiltration_countablePartitionSet (n : ℕ) (t : α) :
    MeasurableSet[countableFiltration α n] (countablePartitionSet n t) :=
  measurableSet_countableFiltration_of_mem n (countablePartitionSet_mem n t)
lemma measurable_countablePartitionSet_subtype (n : ℕ)
    (m : MeasurableSpace (countablePartition α n)) :
    @Measurable α (countablePartition α n) (countableFiltration α n) m
      (fun a ↦ ⟨countablePartitionSet n a, countablePartitionSet_mem n a⟩) :=
  measurable_memPartitionSet_subtype
    (measurableSet_enumerateCountable_countableGeneratingSet (α := α)) n m
lemma measurable_countableFiltration_countablePartitionSet (α : Type*)
    [MeasurableSpace α] [CountablyGenerated α] (n : ℕ) :
    Measurable[countableFiltration α n] (countablePartitionSet n) :=
  measurable_subtype_coe.comp (measurable_countablePartitionSet_subtype _ _)
lemma measurable_countablePartitionSet (α : Type*) [MeasurableSpace α] [CountablyGenerated α]
    (n : ℕ) :
    Measurable (countablePartitionSet (α := α) n) :=
  (measurable_countableFiltration_countablePartitionSet α n).mono ((countableFiltration α).le n)
    le_rfl
lemma iSup_countableFiltration (α : Type*) [m : MeasurableSpace α] [CountablyGenerated α] :
    ⨆ n, countableFiltration α n = m := by
  conv_rhs => rw [← generateFrom_iUnion_countablePartition α, ← iSup_generateFrom]
  rfl
end CountableFiltration
end ProbabilityTheory