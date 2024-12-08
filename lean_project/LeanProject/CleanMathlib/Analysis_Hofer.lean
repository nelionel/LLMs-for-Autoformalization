import Mathlib.Analysis.SpecificLimits.Basic
open Topology Filter Finset
local notation "d" => dist
theorem hofer {X : Type*} [MetricSpace X] [CompleteSpace X] (x : X) (ε : ℝ) (ε_pos : 0 < ε)
    {ϕ : X → ℝ} (cont : Continuous ϕ) (nonneg : ∀ y, 0 ≤ ϕ y) : ∃ ε' > 0, ∃ x' : X,
    ε' ≤ ε ∧ d x' x ≤ 2 * ε ∧ ε * ϕ x ≤ ε' * ϕ x' ∧ ∀ y, d x' y ≤ ε' → ϕ y ≤ 2 * ϕ x' := by
  by_contra H
  have reformulation : ∀ (x') (k : ℕ), ε * ϕ x ≤ ε / 2 ^ k * ϕ x' ↔ 2 ^ k * ϕ x ≤ ϕ x' := by
    intro x' k
    rw [div_mul_eq_mul_div, le_div_iff₀, mul_assoc, mul_le_mul_left ε_pos, mul_comm]
    positivity
  replace H : ∀ k : ℕ, ∀ x', d x' x ≤ 2 * ε ∧ 2 ^ k * ϕ x ≤ ϕ x' →
      ∃ y, d x' y ≤ ε / 2 ^ k ∧ 2 * ϕ x' < ϕ y := by
    intro k x'
    push_neg at H
    have := H (ε / 2 ^ k) (by positivity) x' (div_le_self ε_pos.le <| one_le_pow₀ one_le_two)
    simpa [reformulation] using this
  haveI : Nonempty X := ⟨x⟩
  choose! F hF using H
  let u : ℕ → X := fun n => Nat.recOn n x F
  have hu :
    ∀ n,
      d (u n) x ≤ 2 * ε ∧ 2 ^ n * ϕ x ≤ ϕ (u n) →
        d (u n) (u <| n + 1) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u <| n + 1) := by
    exact fun n ↦ hF n (u n)
  have key : ∀ n, d (u n) (u (n + 1)) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u (n + 1)) := by
    intro n
    induction n using Nat.case_strong_induction_on with
    | hz => simpa [u, ε_pos.le] using hu 0
    | hi n IH =>
      have A : d (u (n + 1)) x ≤ 2 * ε := by
        rw [dist_comm]
        let r := range (n + 1) 
        calc
          d (u 0) (u (n + 1)) ≤ ∑ i ∈ r, d (u i) (u <| i + 1) := dist_le_range_sum_dist u (n + 1)
          _ ≤ ∑ i ∈ r, ε / 2 ^ i :=
            (sum_le_sum fun i i_in => (IH i <| Nat.lt_succ_iff.mp <| Finset.mem_range.mp i_in).1)
          _ = (∑ i ∈ r, (1 / 2 : ℝ) ^ i) * ε := by
            rw [Finset.sum_mul]
            field_simp
          _ ≤ 2 * ε := by gcongr; apply sum_geometric_two_le
      have B : 2 ^ (n + 1) * ϕ x ≤ ϕ (u (n + 1)) := by
        refine @geom_le (ϕ ∘ u) _ zero_le_two (n + 1) fun m hm => ?_
        exact (IH _ <| Nat.lt_add_one_iff.1 hm).2.le
      exact hu (n + 1) ⟨A, B⟩
  cases' forall_and.mp key with key₁ key₂
  have cauchy_u : CauchySeq u := by
    refine cauchySeq_of_le_geometric _ ε one_half_lt_one fun n => ?_
    simpa only [one_div, inv_pow] using key₁ n
  obtain ⟨y, limy⟩ : ∃ y, Tendsto u atTop (𝓝 y) := CompleteSpace.complete cauchy_u
  have lim_top : Tendsto (ϕ ∘ u) atTop atTop := by
    let v n := (ϕ ∘ u) (n + 1)
    suffices Tendsto v atTop atTop by rwa [tendsto_add_atTop_iff_nat] at this
    have hv₀ : 0 < v 0 := by
      calc
        0 ≤ 2 * ϕ (u 0) := by specialize nonneg x; positivity
        _ < ϕ (u (0 + 1)) := key₂ 0
    apply tendsto_atTop_of_geom_le hv₀ one_lt_two
    exact fun n => (key₂ (n + 1)).le
  have lim : Tendsto (ϕ ∘ u) atTop (𝓝 (ϕ y)) := Tendsto.comp cont.continuousAt limy
  exact not_tendsto_atTop_of_tendsto_nhds lim lim_top