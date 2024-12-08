import Mathlib.MeasureTheory.Measure.MeasureSpace
open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure
open scoped Topology
variable {X : Type*} [PseudoMetricSpace X]
structure VitaliFamily {m : MeasurableSpace X} (μ : Measure X) where
  setsAt :  X → Set (Set X)
  measurableSet : ∀ x : X, ∀ s ∈ setsAt x, MeasurableSet s
  nonempty_interior : ∀ x : X, ∀ s ∈ setsAt x, (interior s).Nonempty
  nontrivial : ∀ (x : X), ∀ ε > (0 : ℝ), ∃ s ∈ setsAt x, s ⊆ closedBall x ε
  covering : ∀ (s : Set X) (f : X → Set (Set X)),
    (∀ x ∈ s, f x ⊆ setsAt x) → (∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ t ∈ f x, t ⊆ closedBall x ε) →
    ∃ t : Set (X × Set X), (∀ p ∈ t, p.1 ∈ s) ∧ (t.PairwiseDisjoint fun p ↦ p.2) ∧
      (∀ p ∈ t, p.2 ∈ f p.1) ∧ μ (s \ ⋃ p ∈ t, p.2) = 0
namespace VitaliFamily
variable {m0 : MeasurableSpace X} {μ : Measure X}
def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩
def FineSubfamilyOn (v : VitaliFamily μ) (f : X → Set (Set X)) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ ε > 0, ∃ t ∈ v.setsAt x ∩ f x, t ⊆ closedBall x ε
namespace FineSubfamilyOn
variable {v : VitaliFamily μ} {f : X → Set (Set X)} {s : Set X} (h : v.FineSubfamilyOn f s)
include h
theorem exists_disjoint_covering_ae :
    ∃ t : Set (X × Set X),
      (∀ p : X × Set X, p ∈ t → p.1 ∈ s) ∧
      (t.PairwiseDisjoint fun p => p.2) ∧
      (∀ p : X × Set X, p ∈ t → p.2 ∈ v.setsAt p.1 ∩ f p.1) ∧
      μ (s \ ⋃ (p : X × Set X) (_ : p ∈ t), p.2) = 0 :=
  v.covering s (fun x => v.setsAt x ∩ f x) (fun _ _ => inter_subset_left) h
protected def index : Set (X × Set X) :=
  h.exists_disjoint_covering_ae.choose
@[nolint unusedArguments]
protected def covering (_h : FineSubfamilyOn v f s) : X × Set X → Set X :=
  fun p => p.2
theorem index_subset : ∀ p : X × Set X, p ∈ h.index → p.1 ∈ s :=
  h.exists_disjoint_covering_ae.choose_spec.1
theorem covering_disjoint : h.index.PairwiseDisjoint h.covering :=
  h.exists_disjoint_covering_ae.choose_spec.2.1
theorem covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x) :=
  (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint
theorem covering_mem {p : X × Set X} (hp : p ∈ h.index) : h.covering p ∈ f p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2
theorem covering_mem_family {p : X × Set X} (hp : p ∈ h.index) : h.covering p ∈ v.setsAt p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1
theorem measure_diff_biUnion : μ (s \ ⋃ p ∈ h.index, h.covering p) = 0 :=
  h.exists_disjoint_covering_ae.choose_spec.2.2.2
theorem index_countable [SecondCountableTopology X] : h.index.Countable :=
  h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)
protected theorem measurableSet_u {p : X × Set X} (hp : p ∈ h.index) :
    MeasurableSet (h.covering p) :=
  v.measurableSet p.1 _ (h.covering_mem_family hp)
theorem measure_le_tsum_of_absolutelyContinuous [SecondCountableTopology X] {ρ : Measure X}
    (hρ : ρ ≪ μ) : ρ s ≤ ∑' p : h.index, ρ (h.covering p) :=
  calc
    ρ s ≤ ρ ((s \ ⋃ p ∈ h.index, h.covering p) ∪ ⋃ p ∈ h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, diff_union_self])
    _ ≤ ρ (s \ ⋃ p ∈ h.index, h.covering p) + ρ (⋃ p ∈ h.index, h.covering p) :=
      (measure_union_le _ _)
    _ = ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_diff_biUnion, zero_add,
        measure_biUnion h.index_countable h.covering_disjoint fun x hx => h.measurableSet_u hx]
theorem measure_le_tsum [SecondCountableTopology X] : μ s ≤ ∑' x : h.index, μ (h.covering x) :=
  h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl
end FineSubfamilyOn
def enlarge (v : VitaliFamily μ) (δ : ℝ) (δpos : 0 < δ) : VitaliFamily μ where
  setsAt x := v.setsAt x ∪ {s | MeasurableSet s ∧ (interior s).Nonempty ∧ ¬s ⊆ closedBall x δ}
  measurableSet := by
    rintro x s (hs | hs)
    exacts [v.measurableSet _ _ hs, hs.1]
  nonempty_interior := by
    rintro x s (hs | hs)
    exacts [v.nonempty_interior _ _ hs, hs.2.1]
  nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨s, hs, h's⟩
    exact ⟨s, mem_union_left _ hs, h's⟩
  covering := by
    intro s f fset ffine
    let g : X → Set (Set X) := fun x => f x ∩ v.setsAt x
    have : ∀ x ∈ s, ∀ ε : ℝ, ε > 0 → ∃ t ∈ g x, t ⊆ closedBall x ε := by
      intro x hx ε εpos
      obtain ⟨t, tf, ht⟩ : ∃ t ∈ f x, t ⊆ closedBall x (min ε δ) :=
        ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx tf with (h't | h't)
      · exact ⟨t, ⟨tf, h't⟩, ht.trans (closedBall_subset_closedBall (min_le_left _ _))⟩
      · refine False.elim (h't.2.2 ?_)
        exact ht.trans (closedBall_subset_closedBall (min_le_right _ _))
    rcases v.covering s g (fun x _ => inter_subset_right) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩
variable (v : VitaliFamily μ)
def filterAt (x : X) : Filter (Set X) := (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)
theorem _root_.Filter.HasBasis.vitaliFamily {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : (v.filterAt x).HasBasis p (fun i ↦ {t ∈ v.setsAt x | t ⊆ s i}) := by
  simpa only [← Set.setOf_inter_eq_sep] using h.smallSets.inf_principal _
theorem filterAt_basis_closedBall (x : X) :
    (v.filterAt x).HasBasis (0 < ·) ({t ∈ v.setsAt x | t ⊆ closedBall x ·}) :=
  nhds_basis_closedBall.vitaliFamily v
theorem mem_filterAt_iff {x : X} {s : Set (Set X)} :
    s ∈ v.filterAt x ↔ ∃ ε > (0 : ℝ), ∀ t ∈ v.setsAt x, t ⊆ closedBall x ε → t ∈ s := by
  simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_setOf]
instance filterAt_neBot (x : X) : (v.filterAt x).NeBot :=
  (v.filterAt_basis_closedBall x).neBot_iff.2 <| v.nontrivial _ _
theorem eventually_filterAt_iff {x : X} {P : Set X → Prop} :
    (∀ᶠ t in v.filterAt x, P t) ↔ ∃ ε > (0 : ℝ), ∀ t ∈ v.setsAt x, t ⊆ closedBall x ε → P t :=
  v.mem_filterAt_iff
theorem tendsto_filterAt_iff {ι : Type*} {l : Filter ι} {f : ι → Set X} {x : X} :
    Tendsto f l (v.filterAt x) ↔
      (∀ᶠ i in l, f i ∈ v.setsAt x) ∧ ∀ ε > (0 : ℝ), ∀ᶠ i in l, f i ⊆ closedBall x ε := by
  simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
    tendsto_principal, and_comm, mem_powerset_iff]
theorem eventually_filterAt_mem_setsAt (x : X) : ∀ᶠ t in v.filterAt x, t ∈ v.setsAt x :=
  (v.tendsto_filterAt_iff.mp tendsto_id).1
theorem eventually_filterAt_subset_closedBall (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Set X in v.filterAt x, t ⊆ closedBall x ε :=
  (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε
theorem eventually_filterAt_measurableSet (x : X) : ∀ᶠ t in v.filterAt x, MeasurableSet t := by
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with _ ha using v.measurableSet _ _ ha
theorem frequently_filterAt_iff {x : X} {P : Set X → Prop} :
    (∃ᶠ t in v.filterAt x, P t) ↔ ∀ ε > (0 : ℝ), ∃ t ∈ v.setsAt x, t ⊆ closedBall x ε ∧ P t := by
  simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_setOf]
theorem eventually_filterAt_subset_of_nhds {x : X} {o : Set X} (hx : o ∈ 𝓝 x) :
    ∀ᶠ t in v.filterAt x, t ⊆ o :=
  (eventually_smallSets_subset.2 hx).filter_mono inf_le_left
theorem fineSubfamilyOn_of_frequently (v : VitaliFamily μ) (f : X → Set (Set X)) (s : Set X)
    (h : ∀ x ∈ s, ∃ᶠ t in v.filterAt x, t ∈ f x) : v.FineSubfamilyOn f s := by
  intro x hx ε εpos
  obtain ⟨t, tv, ht, tf⟩ : ∃ t ∈ v.setsAt x, t ⊆ closedBall x ε ∧ t ∈ f x :=
    v.frequently_filterAt_iff.1 (h x hx) ε εpos
  exact ⟨t, ⟨tv, tf⟩, ht⟩
end VitaliFamily