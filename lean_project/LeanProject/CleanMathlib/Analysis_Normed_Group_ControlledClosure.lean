import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Analysis.SpecificLimits.Normed
open Filter Finset
open Topology
variable {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
variable {H : Type*} [NormedAddCommGroup H]
theorem controlled_closure_of_complete {f : NormedAddGroupHom G H} {K : AddSubgroup H} {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hyp : f.SurjectiveOnWith K C) :
    f.SurjectiveOnWith K.topologicalClosure (C + ε) := by
  rintro (h : H) (h_in : h ∈ K.topologicalClosure)
  by_cases hyp_h : h = 0
  · rw [hyp_h]
    use 0
    simp
  set b : ℕ → ℝ := fun i => (1 / 2) ^ i * (ε * ‖h‖ / 2) / C
  have b_pos (i) : 0 < b i := by field_simp [b, hC, hyp_h]
  obtain
    ⟨v : ℕ → H, lim_v : Tendsto (fun n : ℕ => ∑ k ∈ range (n + 1), v k) atTop (𝓝 h), v_in :
      ∀ n, v n ∈ K, hv₀ : ‖v 0 - h‖ < b 0, hv : ∀ n > 0, ‖v n‖ < b n⟩ :=
    controlled_sum_of_mem_closure h_in b_pos
  have : ∀ n, ∃ m' : G, f m' = v n ∧ ‖m'‖ ≤ C * ‖v n‖ := fun n : ℕ => hyp (v n) (v_in n)
  choose u hu hnorm_u using this
  set s : ℕ → G := fun n => ∑ k ∈ range (n + 1), u k
  have : CauchySeq s := by
    apply NormedAddCommGroup.cauchy_series_of_le_geometric'' (by norm_num) one_half_lt_one
    · rintro n (hn : n ≥ 1)
      calc
        ‖u n‖ ≤ C * ‖v n‖ := hnorm_u n
        _ ≤ C * b n := by gcongr; exact (hv _ <| Nat.succ_le_iff.mp hn).le
        _ = (1 / 2) ^ n * (ε * ‖h‖ / 2) := by simp [mul_div_cancel₀ _ hC.ne.symm]
        _ = ε * ‖h‖ / 2 * (1 / 2) ^ n := mul_comm _ _
  obtain ⟨g : G, hg⟩ := cauchySeq_tendsto_of_complete this
  refine ⟨g, ?_, ?_⟩
  · 
    have : f ∘ s = fun n => ∑ k ∈ range (n + 1), v k := by
      ext n
      simp [s, map_sum, hu]
    rw [← this] at lim_v
    exact tendsto_nhds_unique ((f.continuous.tendsto g).comp hg) lim_v
  · 
    suffices ∀ n, ‖s n‖ ≤ (C + ε) * ‖h‖ from
      le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp hg) this
    intro n
    have hnorm₀ : ‖u 0‖ ≤ C * b 0 + C * ‖h‖ := by
      have :=
        calc
          ‖v 0‖ ≤ ‖h‖ + ‖v 0 - h‖ := norm_le_insert' _ _
          _ ≤ ‖h‖ + b 0 := by gcongr
      calc
        ‖u 0‖ ≤ C * ‖v 0‖ := hnorm_u 0
        _ ≤ C * (‖h‖ + b 0) := by gcongr
        _ = C * b 0 + C * ‖h‖ := by rw [add_comm, mul_add]
    have : (∑ k ∈ range (n + 1), C * b k) ≤ ε * ‖h‖ :=
      calc (∑ k ∈ range (n + 1), C * b k)
        _ = (∑ k ∈ range (n + 1), (1 / 2 : ℝ) ^ k) * (ε * ‖h‖ / 2) := by
          simp only [mul_div_cancel₀ _ hC.ne.symm, ← sum_mul]
        _ ≤ 2 * (ε * ‖h‖ / 2) := by gcongr; apply sum_geometric_two_le
        _ = ε * ‖h‖ := mul_div_cancel₀ _ two_ne_zero
    calc
      ‖s n‖ ≤ ∑ k ∈ range (n + 1), ‖u k‖ := norm_sum_le _ _
      _ = (∑ k ∈ range n, ‖u (k + 1)‖) + ‖u 0‖ := sum_range_succ' _ _
      _ ≤ (∑ k ∈ range n, C * ‖v (k + 1)‖) + ‖u 0‖ := by gcongr; apply hnorm_u
      _ ≤ (∑ k ∈ range n, C * b (k + 1)) + (C * b 0 + C * ‖h‖) := by
        gcongr with k; exact (hv _ k.succ_pos).le
      _ = (∑ k ∈ range (n + 1), C * b k) + C * ‖h‖ := by rw [← add_assoc, sum_range_succ']
      _ ≤ (C + ε) * ‖h‖ := by
        rw [add_comm, add_mul]
        apply add_le_add_left this
theorem controlled_closure_range_of_complete {f : NormedAddGroupHom G H} {K : Type*}
    [SeminormedAddCommGroup K] {j : NormedAddGroupHom K H} (hj : ∀ x, ‖j x‖ = ‖x‖) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hyp : ∀ k, ∃ g, f g = j k ∧ ‖g‖ ≤ C * ‖k‖) :
    f.SurjectiveOnWith j.range.topologicalClosure (C + ε) := by
  replace hyp : ∀ h ∈ j.range, ∃ g, f g = h ∧ ‖g‖ ≤ C * ‖h‖ := by
    intro h h_in
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
  exact controlled_closure_of_complete hC hε hyp