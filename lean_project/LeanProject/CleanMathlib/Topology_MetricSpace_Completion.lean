import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Instances.Real
open Set Filter UniformSpace Metric
open Filter Topology Uniformity
noncomputable section
universe u v
variable {α : Type u} {β : Type v} [PseudoMetricSpace α]
namespace UniformSpace.Completion
instance : Dist (Completion α) :=
  ⟨Completion.extension₂ dist⟩
protected theorem uniformContinuous_dist :
    UniformContinuous fun p : Completion α × Completion α ↦ dist p.1 p.2 :=
  uniformContinuous_extension₂ dist
protected theorem continuous_dist [TopologicalSpace β] {f g : β → Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ dist (f x) (g x) :=
  Completion.uniformContinuous_dist.continuous.comp (hf.prod_mk hg : _)
@[simp]
protected theorem dist_eq (x y : α) : dist (x : Completion α) y = dist x y :=
  Completion.extension₂_coe_coe uniformContinuous_dist _ _
protected theorem dist_self (x : Completion α) : dist x x = 0 := by
  refine induction_on x ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    exact Completion.continuous_dist continuous_id continuous_id
  · intro a
    rw [Completion.dist_eq, dist_self]
protected theorem dist_comm (x y : Completion α) : dist x y = dist y x := by
  refine induction_on₂ x y ?_ ?_
  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
        (Completion.continuous_dist continuous_snd continuous_fst)
  · intro a b
    rw [Completion.dist_eq, Completion.dist_eq, dist_comm]
protected theorem dist_triangle (x y z : Completion α) : dist x z ≤ dist x y + dist y z := by
  refine induction_on₃ x y z ?_ ?_
  · refine isClosed_le ?_ (Continuous.add ?_ ?_) <;>
      apply_rules [Completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
  · intro a b c
    rw [Completion.dist_eq, Completion.dist_eq, Completion.dist_eq]
    exact dist_triangle a b c
protected theorem mem_uniformity_dist (s : Set (Completion α × Completion α)) :
    s ∈ 𝓤 (Completion α) ↔ ∃ ε > 0, ∀ {a b}, dist a b < ε → (a, b) ∈ s := by
  constructor
  · 
    intro hs
    rcases mem_uniformity_isClosed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩
    have A : { x : α × α | (↑x.1, ↑x.2) ∈ t } ∈ uniformity α :=
      uniformContinuous_def.1 (uniformContinuous_coe α) t ht
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩
    refine ⟨ε, εpos, @fun x y hxy ↦ ?_⟩
    have : ε ≤ dist x y ∨ (x, y) ∈ t := by
      refine induction_on₂ x y ?_ ?_
      · have : { x : Completion α × Completion α | ε ≤ dist x.fst x.snd ∨ (x.fst, x.snd) ∈ t } =
               { p : Completion α × Completion α | ε ≤ dist p.1 p.2 } ∪ t := by ext; simp
        rw [this]
        apply IsClosed.union _ tclosed
        exact isClosed_le continuous_const Completion.uniformContinuous_dist.continuous
      · intro x y
        rw [Completion.dist_eq]
        by_cases h : ε ≤ dist x y
        · exact Or.inl h
        · have Z := hε (not_le.1 h)
          simp only [Set.mem_setOf_eq] at Z
          exact Or.inr Z
    simp only [not_le.mpr hxy, false_or, not_le] at this
    exact ts this
  · 
    rintro ⟨ε, εpos, hε⟩
    let r : Set (ℝ × ℝ) := { p | dist p.1 p.2 < ε }
    have : r ∈ uniformity ℝ := Metric.dist_mem_uniformity εpos
    have T := uniformContinuous_def.1 (@Completion.uniformContinuous_dist α _) r this
    simp only [uniformity_prod_eq_prod, mem_prod_iff, exists_prop, Filter.mem_map,
      Set.mem_setOf_eq] at T
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩
    refine mem_of_superset ht1 ?_
    have A : ∀ a b : Completion α, (a, b) ∈ t1 → dist a b < ε := by
      intro a b hab
      have : ((a, b), (a, a)) ∈ t1 ×ˢ t2 := ⟨hab, refl_mem_uniformity ht2⟩
      have I := ht this
      simp? [r, Completion.dist_self, Real.dist_eq, Completion.dist_comm] at I says
        simp only [Real.dist_eq, mem_setOf_eq, preimage_setOf_eq, Completion.dist_self,
          Completion.dist_comm, zero_sub, abs_neg, r] at I
      exact lt_of_le_of_lt (le_abs_self _) I
    show t1 ⊆ s
    rintro ⟨a, b⟩ hp
    have : dist a b < ε := A a b hp
    exact hε this
protected theorem uniformity_dist' :
    𝓤 (Completion α) = ⨅ ε : { ε : ℝ // 0 < ε }, 𝓟 { p | dist p.1 p.2 < ε.val } := by
  ext s; rw [mem_iInf_of_directed]
  · simp [Completion.mem_uniformity_dist, subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    use ⟨min r p, lt_min hr hp⟩
    simp +contextual [lt_min_iff]
protected theorem uniformity_dist : 𝓤 (Completion α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε } := by
  simpa [iInf_subtype] using @Completion.uniformity_dist' α _
instance instMetricSpace : MetricSpace (Completion α) :=
  @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist } _
@[deprecated eq_of_dist_eq_zero (since := "2024-03-10")]
protected theorem eq_of_dist_eq_zero (x y : Completion α) (h : dist x y = 0) : x = y :=
  eq_of_dist_eq_zero h
theorem coe_isometry : Isometry ((↑) : α → Completion α) :=
  Isometry.of_dist_eq Completion.dist_eq
@[simp]
protected theorem edist_eq (x y : α) : edist (x : Completion α) y = edist x y :=
  coe_isometry x y
instance {M} [Zero M] [Zero α] [SMul M α] [PseudoMetricSpace M] [BoundedSMul M α] :
    BoundedSMul M (Completion α) where
  dist_smul_pair' c x₁ x₂ := by
    induction x₁, x₂ using induction_on₂ with
    | hp =>
      exact isClosed_le
        ((continuous_fst.const_smul _).dist (continuous_snd.const_smul _))
        (continuous_const.mul (continuous_fst.dist continuous_snd))
    | ih x₁ x₂ =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq,  Completion.dist_eq]
      exact dist_smul_pair c x₁ x₂
  dist_pair_smul' c₁ c₂ x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_le
        ((continuous_const_smul _).dist (continuous_const_smul _))
        (continuous_const.mul (continuous_id.dist continuous_const))
    | ih x =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq, ← coe_zero, Completion.dist_eq]
      exact dist_pair_smul c₁ c₂ x
end UniformSpace.Completion
open UniformSpace Completion NNReal
theorem LipschitzWith.completion_extension [MetricSpace β] [CompleteSpace β] {f : α → β}
    {K : ℝ≥0} (h : LipschitzWith K f) : LipschitzWith K (Completion.extension f) :=
  LipschitzWith.of_dist_le_mul fun x y => induction_on₂ x y
    (isClosed_le (by fun_prop) (by fun_prop)) <| by
      simpa only [extension_coe h.uniformContinuous, Completion.dist_eq] using h.dist_le_mul
theorem LipschitzWith.completion_map [PseudoMetricSpace β] {f : α → β} {K : ℝ≥0}
    (h : LipschitzWith K f) : LipschitzWith K (Completion.map f) :=
  one_mul K ▸ (coe_isometry.lipschitz.comp h).completion_extension
theorem Isometry.completion_extension [MetricSpace β] [CompleteSpace β] {f : α → β}
    (h : Isometry f) : Isometry (Completion.extension f) :=
  Isometry.of_dist_eq fun x y => induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun _ _ ↦ by
      simp only [extension_coe h.uniformContinuous, Completion.dist_eq, h.dist_eq]
theorem Isometry.completion_map [PseudoMetricSpace β] {f : α → β}
    (h : Isometry f) : Isometry (Completion.map f) :=
  (coe_isometry.comp h).completion_extension