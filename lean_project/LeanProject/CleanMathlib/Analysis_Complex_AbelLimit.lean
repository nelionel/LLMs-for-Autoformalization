import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Peel
import Mathlib.Tactic.Positivity
open Filter Finset
open scoped Topology
namespace Complex
section StolzSet
open Real
def stolzSet (M : ℝ) : Set ℂ := {z | ‖z‖ < 1 ∧ ‖1 - z‖ < M * (1 - ‖z‖)}
def stolzCone (s : ℝ) : Set ℂ := {z | |z.im| < s * (1 - z.re)}
theorem stolzSet_empty {M : ℝ} (hM : M ≤ 1) : stolzSet M = ∅ := by
  ext z
  rw [stolzSet, Set.mem_setOf, Set.mem_empty_iff_false, iff_false, not_and, not_lt, ← sub_pos]
  intro zn
  calc
    _ ≤ 1 * (1 - ‖z‖) := mul_le_mul_of_nonneg_right hM zn.le
    _ = ‖(1 : ℂ)‖ - ‖z‖ := by rw [one_mul, norm_one]
    _ ≤ _ := norm_sub_norm_le _ _
theorem nhdsWithin_lt_le_nhdsWithin_stolzSet {M : ℝ} (hM : 1 < M) :
    (𝓝[<] 1).map ofReal ≤ 𝓝[stolzSet M] 1 := by
  rw [← tendsto_id']
  refine tendsto_map' <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ofReal
    (tendsto_nhdsWithin_of_tendsto_nhds <| ofRealCLM.continuous.tendsto' 1 1 rfl) ?_
  simp only [eventually_iff, norm_eq_abs, abs_ofReal, abs_lt, mem_nhdsWithin]
  refine ⟨Set.Ioo 0 2, isOpen_Ioo, by norm_num, fun x hx ↦ ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio] at hx
  simp only [Set.mem_setOf_eq, stolzSet, ← ofReal_one, ← ofReal_sub, norm_eq_abs, abs_ofReal,
    abs_of_pos hx.1.1, abs_of_pos <| sub_pos.mpr hx.2]
  exact ⟨hx.2, lt_mul_left (sub_pos.mpr hx.2) hM⟩
private lemma stolzCone_subset_stolzSet_aux' (s : ℝ) :
    ∃ M ε, 0 < M ∧ 0 < ε ∧ ∀ x y, 0 < x → x < ε → |y| < s * x →
      sqrt (x ^ 2 + y ^ 2) < M * (1 - sqrt ((1 - x) ^ 2 + y ^ 2)) := by
  refine ⟨2 * sqrt (1 + s ^ 2) + 1, 1 / (1 + s ^ 2), by positivity, by positivity,
    fun x y hx₀ hx₁ hy ↦ ?_⟩
  have H : sqrt ((1 - x) ^ 2 + y ^ 2) ≤ 1 - x / 2 := by
    calc sqrt ((1 - x) ^ 2 + y ^ 2)
      _ ≤ sqrt ((1 - x) ^ 2 + (s * x) ^ 2) := sqrt_le_sqrt <| by rw [← _root_.sq_abs y]; gcongr
      _ = sqrt (1 - 2 * x + (1 + s ^ 2) * x * x) := by congr 1; ring
      _ ≤ sqrt (1 - 2 * x + (1 + s ^ 2) * (1 / (1 + s ^ 2)) * x) := sqrt_le_sqrt <| by gcongr
      _ = sqrt (1 - x) := by congr 1; field_simp; ring
      _ ≤ 1 - x / 2 := by
        simp_rw [sub_eq_add_neg, ← neg_div]
        refine sqrt_one_add_le <| neg_le_neg_iff.mpr (hx₁.trans_le ?_).le
        rw [div_le_one (by positivity)]
        exact le_add_of_nonneg_right <| sq_nonneg s
  calc sqrt (x ^ 2 + y ^ 2)
    _ ≤ sqrt (x ^ 2 + (s * x) ^ 2) := sqrt_le_sqrt <| by rw [← _root_.sq_abs y]; gcongr
    _ = sqrt ((1 + s ^ 2) * x ^ 2) := by congr; ring
    _ = sqrt (1 + s ^ 2) * x := by rw [sqrt_mul' _ (sq_nonneg x), sqrt_sq hx₀.le]
    _ = 2 * sqrt (1 + s ^ 2) * (x / 2) := by ring
    _ < (2 * sqrt (1 + s ^ 2) + 1) * (x / 2) := by gcongr; exact lt_add_one _
    _ ≤ _ := by gcongr; exact le_sub_comm.mpr H
lemma stolzCone_subset_stolzSet_aux {s : ℝ} (hs : 0 < s) :
    ∃ M ε, 0 < M ∧ 0 < ε ∧ {z : ℂ | 1 - ε < z.re} ∩ stolzCone s ⊆ stolzSet M := by
  peel stolzCone_subset_stolzSet_aux' s with M ε hM hε H
  rintro z ⟨hzl, hzr⟩
  rw [Set.mem_setOf_eq, sub_lt_comm, ← one_re, ← sub_re] at hzl
  rw [stolzCone, Set.mem_setOf_eq, ← one_re, ← sub_re] at hzr
  replace H :=
    H (1 - z).re z.im ((mul_pos_iff_of_pos_left hs).mp <| (abs_nonneg z.im).trans_lt hzr) hzl hzr
  have h : z.im ^ 2 = (1 - z).im ^ 2 := by
    simp only [sub_im, one_im, zero_sub, even_two, neg_sq]
  rw [h, ← abs_eq_sqrt_sq_add_sq, ← norm_eq_abs, ← h, sub_re, one_re, sub_sub_cancel,
    ← abs_eq_sqrt_sq_add_sq, ← norm_eq_abs] at H
  exact ⟨sub_pos.mp <| (mul_pos_iff_of_pos_left hM).mp <| (norm_nonneg _).trans_lt H, H⟩
lemma nhdsWithin_stolzCone_le_nhdsWithin_stolzSet {s : ℝ} (hs : 0 < s) :
    ∃ M, 𝓝[stolzCone s] 1 ≤ 𝓝[stolzSet M] 1 := by
  obtain ⟨M, ε, _, hε, H⟩ := stolzCone_subset_stolzSet_aux hs
  use M
  rw [nhdsWithin_le_iff, mem_nhdsWithin]
  refine ⟨{w | 1 - ε < w.re}, isOpen_lt continuous_const continuous_re, ?_, H⟩
  simp only [Set.mem_setOf_eq, one_re, sub_lt_self_iff, hε]
end StolzSet
variable {f : ℕ → ℂ} {l : ℂ}
lemma abel_aux (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun n ↦ (1 - z) * ∑ i ∈ range n, (l - ∑ j ∈ range (i + 1), f j) * z ^ i)
      atTop (𝓝 (l - ∑' n, f n * z ^ n)) := by
  let s := fun n ↦ ∑ i ∈ range n, f i
  have k := h.sub (summable_powerSeries_of_norm_lt_one h.cauchySeq hz).hasSum.tendsto_sum_nat
  simp_rw [← sum_sub_distrib, ← mul_one_sub, ← geom_sum_mul_neg, ← mul_assoc, ← sum_mul,
    mul_comm, mul_sum _ _ (f _), range_eq_Ico, ← sum_Ico_Ico_comm', ← range_eq_Ico,
    ← sum_mul] at k
  conv at k =>
    enter [1, n]
    rw [sum_congr (g := fun j ↦ (∑ k ∈ range n, f k - ∑ k ∈ range (j + 1), f k) * z ^ j)
      rfl (fun j hj ↦ by congr 1; exact sum_Ico_eq_sub _ (mem_range.mp hj))]
  suffices Tendsto (fun n ↦ (l - s n) * ∑ i ∈ range n, z ^ i) atTop (𝓝 0) by
    simp_rw [mul_sum] at this
    replace this := (this.const_mul (1 - z)).add k
    conv at this =>
      enter [1, n]
      rw [← mul_add, ← sum_add_distrib]
      enter [2, 2, i]
      rw [← add_mul, sub_add_sub_cancel]
    rwa [mul_zero, zero_add] at this
  rw [← zero_mul (-1 / (z - 1))]
  apply Tendsto.mul
  · simpa only [neg_zero, neg_sub] using (tendsto_sub_nhds_zero_iff.mpr h).neg
  · conv =>
      enter [1, n]
      rw [geom_sum_eq (by contrapose! hz; simp [hz]), sub_div, sub_eq_add_neg, ← neg_div]
    rw [← zero_add (-1 / (z - 1)), ← zero_div (z - 1)]
    apply Tendsto.add (Tendsto.div_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz) (z - 1))
    simp only [zero_div, zero_add, tendsto_const_nhds_iff]
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzSet
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) {M : ℝ} :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) (𝓝[stolzSet M] 1) (𝓝 l) := by
  cases' le_or_lt M 1 with hM hM
  · simp_rw [stolzSet_empty hM, nhdsWithin_empty, tendsto_bot]
  let s := fun n ↦ ∑ i ∈ range n, f i
  let g := fun z ↦ ∑' n, f n * z ^ n
  have hm := Metric.tendsto_atTop.mp h
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm] at hm ⊢
  intro ε εpos
  obtain ⟨B₁, hB₁⟩ := hm (ε / 4 / M) (by positivity)
  let F := ∑ i ∈ range B₁, ‖l - s (i + 1)‖
  use ε / 4 / (F + 1), by positivity
  intro z ⟨zn, zm⟩ zd
  have p := abel_aux h zn
  simp_rw [Metric.tendsto_atTop, dist_eq_norm, norm_sub_rev] at p
  obtain ⟨B₂, hB₂⟩ := p (ε / 2) (by positivity)
  clear hm p
  replace hB₂ := hB₂ (max B₁ B₂) (by simp)
  suffices ‖(1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ < ε / 2 by
    calc
      _ = ‖l - g z‖ := by rw [norm_sub_rev]
      _ = ‖l - g z - (1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i +
          (1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by rw [sub_add_cancel _]
      _ ≤ ‖l - g z - (1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ +
          ‖(1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB₂ this
      _ = _ := add_halves ε
  calc
    _ = ‖(1 - z) * ∑ i ∈ range B₁, (l - s (i + 1)) * z ^ i +
        (1 - z) * ∑ i ∈ Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [← mul_add, sum_range_add_sum_Ico _ (le_max_left B₁ B₂)]
    _ ≤ ‖(1 - z) * ∑ i ∈ range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖(1 - z) * ∑ i ∈ Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖∑ i ∈ range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖1 - z‖ * ‖∑ i ∈ Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖1 - z‖ * ∑ i ∈ range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i +
        ‖1 - z‖ * ∑ i ∈ Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i := by
      gcongr <;> simp_rw [← norm_pow, ← norm_mul, norm_sum_le]
  have S₁ : ‖1 - z‖ * ∑ i ∈ range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i ∈ range B₁, ‖l - s (i + 1)‖ := by
        gcongr; nth_rw 3 [← mul_one ‖_‖]
        gcongr; exact pow_le_one₀ (norm_nonneg _) zn.le
      _ ≤ ‖1 - z‖ * (F + 1) := by gcongr; linarith only
      _ < _ := by rwa [norm_sub_rev, lt_div_iff₀ (by positivity)] at zd
  have S₂ : ‖1 - z‖ * ∑ i ∈ Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i ∈ Ico B₁ (max B₁ B₂), ε / 4 / M * ‖z‖ ^ i := by
        gcongr with i hi
        have := hB₁ (i + 1) (by linarith only [(mem_Ico.mp hi).1])
        rw [norm_sub_rev] at this
        exact this.le
      _ = ‖1 - z‖ * (ε / 4 / M) * ∑ i ∈ Ico B₁ (max B₁ B₂), ‖z‖ ^ i := by
        rw [← mul_sum, ← mul_assoc]
      _ ≤ ‖1 - z‖ * (ε / 4 / M) * ∑' i, ‖z‖ ^ i := by
        gcongr
        exact sum_le_tsum _ (fun _ _ ↦ by positivity)
          (summable_geometric_of_lt_one (by positivity) zn)
      _ = ‖1 - z‖ * (ε / 4 / M) / (1 - ‖z‖) := by
        rw [tsum_geometric_of_lt_one (by positivity) zn, ← div_eq_mul_inv]
      _ < M * (1 - ‖z‖) * (ε / 4 / M) / (1 - ‖z‖) := by gcongr; linarith only [zn]
      _ = _ := by
        rw [← mul_rotate, mul_div_cancel_right₀ _ (by linarith only [zn]),
          div_mul_cancel₀ _ (by linarith only [hM])]
  convert add_lt_add S₁ S₂ using 1
  linarith only
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzCone
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) (𝓝[stolzCone s] 1) (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet h).mono_left
    (nhdsWithin_stolzCone_le_nhdsWithin_stolzSet hs).choose_spec
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) ((𝓝[<] 1).map ofReal) (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2) h).mono_left
    (nhdsWithin_lt_le_nhdsWithin_stolzSet one_lt_two)
end Complex
namespace Real
open Complex
variable {f : ℕ → ℝ} {l : ℝ}
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x ↦ ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l) := by
  have m : (𝓝 l).map ofReal ≤ 𝓝 ↑l := ofRealCLM.continuous.tendsto l
  replace h := (tendsto_map.comp h).mono_right m
  rw [Function.comp_def] at h
  push_cast at h
  replace h := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [tendsto_map'_iff] at h
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  convert h
  simp_rw [Function.comp_apply, dist_eq_norm]
  norm_cast
end Real