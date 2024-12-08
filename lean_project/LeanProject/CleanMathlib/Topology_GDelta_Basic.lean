import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.Basic
assert_not_exists UniformSpace
noncomputable section
open Topology TopologicalSpace Filter Encodable Set
variable {X Y ι : Type*} {ι' : Sort*}
section IsGδ
variable [TopologicalSpace X]
def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
theorem IsOpen.isGδ {s : Set X} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩
@[simp]
protected theorem IsGδ.empty : IsGδ (∅ : Set X) :=
  isOpen_empty.isGδ
@[deprecated (since := "2024-02-15")] alias isGδ_empty := IsGδ.empty
@[simp]
protected theorem IsGδ.univ : IsGδ (univ : Set X) :=
  isOpen_univ.isGδ
@[deprecated (since := "2024-02-15")] alias isGδ_univ := IsGδ.univ
theorem IsGδ.biInter_of_isOpen {I : Set ι} (hI : I.Countable) {f : ι → Set X}
    (hf : ∀ i ∈ I, IsOpen (f i)) : IsGδ (⋂ i ∈ I, f i) :=
  ⟨f '' I, by rwa [forall_mem_image], hI.image _, by rw [sInter_image]⟩
@[deprecated (since := "2024-02-15")] alias isGδ_biInter_of_isOpen := IsGδ.biInter_of_isOpen
theorem IsGδ.iInter_of_isOpen [Countable ι'] {f : ι' → Set X} (hf : ∀ i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_mem_range], countable_range _, by rw [sInter_range]⟩
@[deprecated (since := "2024-02-15")] alias isGδ_iInter_of_isOpen := IsGδ.iInter_of_isOpen
lemma isGδ_iff_eq_iInter_nat {s : Set X} :
    IsGδ s ↔ ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ s = ⋂ n, f n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl|hT
    · exact ⟨fun _n ↦ univ, fun _n ↦ isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : ∃ (f : ℕ → Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by aesop, by simp [hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact .iInter_of_isOpen hf
alias ⟨IsGδ.eq_iInter_nat, _⟩ := isGδ_iff_eq_iInter_nat
protected theorem IsGδ.iInter [Countable ι'] {s : ι' → Set X} (hs : ∀ i, IsGδ (s i)) :
    IsGδ (⋂ i, s i) := by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine ⟨⋃ i, T i, ?_, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  simpa [@forall_swap ι'] using hTo
@[deprecated (since := "2024.02.15")] alias isGδ_iInter := IsGδ.iInter
theorem IsGδ.biInter {s : Set ι} (hs : s.Countable) {t : ∀ i ∈ s, Set X}
    (ht : ∀ (i) (hi : i ∈ s), IsGδ (t i hi)) : IsGδ (⋂ i ∈ s, t i ‹_›) := by
  rw [biInter_eq_iInter]
  haveI := hs.to_subtype
  exact .iInter fun x => ht x x.2
@[deprecated (since := "2024-02-15")] alias isGδ_biInter := IsGδ.biInter
theorem IsGδ.sInter {S : Set (Set X)} (h : ∀ s ∈ S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_biInter] using IsGδ.biInter hS h
@[deprecated (since := "2024-02-15")] alias isGδ_sInter := IsGδ.sInter
theorem IsGδ.inter {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∩ t) := by
  rw [inter_eq_iInter]
  exact .iInter (Bool.forall_bool.2 ⟨ht, hs⟩)
theorem IsGδ.union {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s ∪ t) := by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  refine .biInter_of_isOpen (Scount.prod Tcount) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)
theorem IsGδ.sUnion {S : Set (Set X)} (hS : S.Finite) (h : ∀ s ∈ S, IsGδ s) : IsGδ (⋃₀ S) := by
  induction S, hS using Set.Finite.dinduction_on with
  | H0 => simp
  | H1 _ _ ih =>
    simp only [forall_mem_insert, sUnion_insert] at *
    exact h.1.union (ih h.2)
theorem IsGδ.biUnion {s : Set ι} (hs : s.Finite) {f : ι → Set X} (h : ∀ i ∈ s, IsGδ (f i)) :
    IsGδ (⋃ i ∈ s, f i) := by
  rw [← sUnion_image]
  exact .sUnion (hs.image _) (forall_mem_image.2 h)
@[deprecated (since := "2024-02-15")]
alias isGδ_biUnion := IsGδ.biUnion
theorem IsGδ.iUnion [Finite ι'] {f : ι' → Set X} (h : ∀ i, IsGδ (f i)) : IsGδ (⋃ i, f i) :=
  .sUnion (finite_range _) <| forall_mem_range.2 h
end IsGδ
section residual
variable [TopologicalSpace X]
def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }
instance countableInterFilter_residual : CountableInterFilter (residual X) := by
  rw [residual]; infer_instance
theorem residual_of_dense_open {s : Set X} (ho : IsOpen s) (hd : Dense s) : s ∈ residual X :=
  CountableGenerateSets.basic ⟨ho, hd⟩
theorem residual_of_dense_Gδ {s : Set X} (ho : IsGδ s) (hd : Dense s) : s ∈ residual X := by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))
theorem mem_residual_iff {s : Set X} :
    s ∈ residual X ↔
      ∃ S : Set (Set X), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_setOf, forall_and, and_assoc]
end residual
section meagre
open Function TopologicalSpace Set
variable {X : Type*} [TopologicalSpace X]
def IsNowhereDense (s : Set X) := interior (closure s) = ∅
@[simp]
lemma isNowhereDense_empty : IsNowhereDense (∅ : Set X) := by
  rw [IsNowhereDense, closure_empty, interior_empty]
lemma IsClosed.isNowhereDense_iff {s : Set X} (hs : IsClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
  rw [IsNowhereDense, IsClosed.closure_eq hs]
protected lemma IsNowhereDense.closure {s : Set X} (hs : IsNowhereDense s) :
    IsNowhereDense (closure s) := by
  rwa [IsNowhereDense, closure_closure]
lemma IsNowhereDense.subset_of_closed_isNowhereDense {s : Set X} (hs : IsNowhereDense s) :
    ∃ t : Set X, s ⊆ t ∧ IsNowhereDense t ∧ IsClosed t :=
  ⟨closure s, subset_closure, ⟨hs.closure, isClosed_closure⟩⟩
lemma isClosed_isNowhereDense_iff_compl {s : Set X} :
    IsClosed s ∧ IsNowhereDense s ↔ IsOpen sᶜ ∧ Dense sᶜ := by
  rw [and_congr_right IsClosed.isNowhereDense_iff,
    isOpen_compl_iff, interior_eq_empty_iff_dense_compl]
def IsMeagre (s : Set X) := sᶜ ∈ residual X
lemma meagre_empty : IsMeagre (∅ : Set X) := by
  rw [IsMeagre, compl_empty]
  exact Filter.univ_mem
lemma IsMeagre.mono {s t : Set X} (hs : IsMeagre s) (hts : t ⊆ s) : IsMeagre t :=
  Filter.mem_of_superset hs (compl_subset_compl.mpr hts)
lemma IsMeagre.inter {s t : Set X} (hs : IsMeagre s) : IsMeagre (s ∩ t) :=
  hs.mono inter_subset_left
lemma isMeagre_iUnion {s : ℕ → Set X} (hs : ∀ n, IsMeagre (s n)) : IsMeagre (⋃ n, s n) := by
  rw [IsMeagre, compl_iUnion]
  exact countable_iInter_mem.mpr hs
lemma isMeagre_iff_countable_union_isNowhereDense {s : Set X} :
    IsMeagre s ↔ ∃ S : Set (Set X), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ ⋃₀ S := by
  rw [IsMeagre, mem_residual_iff, compl_bijective.surjective.image_surjective.exists]
  simp_rw [← and_assoc, ← forall_and, forall_mem_image, ← isClosed_isNowhereDense_iff_compl,
    sInter_image, ← compl_iUnion₂, compl_subset_compl, ← sUnion_eq_biUnion, and_assoc]
  refine ⟨fun ⟨S, hS, hc, hsub⟩ ↦ ⟨S, fun s hs ↦ (hS hs).2, ?_, hsub⟩, ?_⟩
  · rw [← compl_compl_image S]; exact hc.image _
  · intro ⟨S, hS, hc, hsub⟩
    use closure '' S
    rw [forall_mem_image]
    exact ⟨fun s hs ↦ ⟨isClosed_closure, (hS s hs).closure⟩,
      (hc.image _).image _, hsub.trans (sUnion_mono_subsets fun s ↦ subset_closure)⟩
end meagre