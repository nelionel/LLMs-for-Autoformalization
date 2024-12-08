import Mathlib.Analysis.Normed.Order.UpperLower
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Order.DenselyOrdered
open Filter MeasureTheory Metric Set
open scoped Topology
variable {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)} {x : ι → ℝ}
private lemma aux₀
    (h : ∀ δ, 0 < δ →
      ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s) :
    ¬Tendsto (fun r ↦ volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 0) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine not_eventually.2
    (Frequently.of_forall fun _ ↦ lt_irrefl <| ENNReal.ofReal <| 4⁻¹ ^ Fintype.card ι)
    ((Filter.Tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds ?_).mono fun n ↦
      lt_of_le_of_lt ?_)
  on_goal 2 =>
    calc
      ENNReal.ofReal (4⁻¹ ^ Fintype.card ι)
        = volume (closedBall (f (ε n) (hε' n)) (ε n / 4)) / volume (closedBall x (ε n)) := ?_
      _ ≤ volume (closure s ∩ closedBall x (ε n)) / volume (closedBall x (ε n)) := by
        gcongr
        exact subset_inter ((hf₁ _ <| hε' n).trans interior_subset_closure) <| hf₀ _ <| hε' n
    have := hε' n
    rw [Real.volume_pi_closedBall, Real.volume_pi_closedBall, ← ENNReal.ofReal_div_of_pos,
      ← div_pow, mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals positivity
private lemma aux₁
    (h : ∀ δ, 0 < δ →
      ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior sᶜ) :
    ¬Tendsto (fun r ↦ volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 1) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine not_eventually.2
      (Frequently.of_forall fun _ ↦ lt_irrefl <| 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι))
      ((Filter.Tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) <|
            ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_).mono
        fun n ↦ lt_of_le_of_lt' ?_)
  on_goal 2 =>
    calc
      volume (closure s ∩ closedBall x (ε n)) / volume (closedBall x (ε n))
        ≤ volume (closedBall x (ε n) \ closedBall (f (ε n) <| hε' n) (ε n / 4)) /
          volume (closedBall x (ε n)) := by
        gcongr
        rw [diff_eq_compl_inter]
        refine inter_subset_inter_left _ ?_
        rw [subset_compl_comm, ← interior_compl]
        exact hf₁ _ _
      _ = 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι) := ?_
    dsimp only
    have := hε' n
    rw [measure_diff (hf₀ _ _) _ ((Real.volume_pi_closedBall _ _).trans_ne ENNReal.ofReal_ne_top),
      Real.volume_pi_closedBall, Real.volume_pi_closedBall, ENNReal.sub_div fun _ _ ↦ _,
      ENNReal.div_self _ ENNReal.ofReal_ne_top, ← ENNReal.ofReal_div_of_pos, ← div_pow,
      mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals try positivity
  · simp_all
  · exact measurableSet_closedBall.nullMeasurableSet
theorem IsUpperSet.null_frontier (hs : IsUpperSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x ∈ closure s <;>
    simp only [mem_compl_iff, mem_setOf, h, not_false_eq_true, indicator_of_not_mem,
      indicator_of_mem, Pi.one_apply]
  · refine aux₁ fun _ ↦ hs.compl.exists_subset_ball <| frontier_subset_closure ?_
    rwa [frontier_compl]
  · exact aux₀ fun _ ↦ hs.exists_subset_ball <| frontier_subset_closure hx
theorem IsLowerSet.null_frontier (hs : IsLowerSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x ∈ closure s <;>
    simp only [mem_compl_iff, mem_setOf, h, not_false_eq_true, indicator_of_not_mem,
      indicator_of_mem, Pi.one_apply]
  · refine aux₁ fun _ ↦ hs.compl.exists_subset_ball <| frontier_subset_closure ?_
    rwa [frontier_compl]
  · exact aux₀ fun _ ↦ hs.exists_subset_ball <| frontier_subset_closure hx
theorem Set.OrdConnected.null_frontier (hs : s.OrdConnected) : volume (frontier s) = 0 := by
  rw [← hs.upperClosure_inter_lowerClosure]
  exact measure_mono_null (frontier_inter_subset _ _) <| measure_union_null
    (measure_inter_null_of_null_left _ (UpperSet.upper _).null_frontier)
    (measure_inter_null_of_null_right _ (LowerSet.lower _).null_frontier)
protected theorem Set.OrdConnected.nullMeasurableSet (hs : s.OrdConnected) : NullMeasurableSet s :=
  nullMeasurableSet_of_null_frontier hs.null_frontier
theorem IsAntichain.volume_eq_zero [Nonempty ι] (hs : IsAntichain (· ≤ ·) s) : volume s = 0 := by
  refine measure_mono_null ?_ hs.ordConnected.null_frontier
  rw [← closure_diff_interior, hs.interior_eq_empty, diff_empty]
  exact subset_closure