import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Data.Nat.Choose.Sum
open Metric NNReal
namespace IsUltrametricDist
section sufficient
variable {R : Type*} [NormedDivisionRing R]
lemma isUltrametricDist_of_forall_norm_add_one_le_max_norm_one
    (h : ∀ x : R, ‖x + 1‖ ≤ max ‖x‖ 1) : IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_norm_add_le_max_norm (fun x y ↦ ?_)
  rcases eq_or_ne y 0 with rfl | hy
  · simpa only [add_zero] using le_max_left _ _
  · have p : 0 < ‖y‖ := norm_pos_iff.mpr hy
    simpa only [div_add_one hy, norm_div, div_le_iff₀ p, max_mul_of_nonneg _ _ p.le, one_mul,
      div_mul_cancel₀ _ p.ne'] using h (x / y)
lemma isUltrametricDist_of_forall_norm_add_one_of_norm_le_one
    (h : ∀ x : R, ‖x‖ ≤ 1 → ‖x + 1‖ ≤ 1) : IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_norm_add_one_le_max_norm_one fun x ↦ ?_
  rcases le_or_lt ‖x‖ 1 with H|H
  · exact (h _ H).trans (le_max_right _ _)
  · suffices ‖x + 1‖ ≤ ‖x‖ from this.trans (le_max_left _ _)
    rw [← div_le_one (by positivity), ← norm_div, add_div,
      div_self (by simpa using H.trans' zero_lt_one), add_comm]
    apply h
    simp [inv_le_one_iff₀, H.le]
lemma isUltrametricDist_of_forall_norm_sub_one_of_norm_le_one
    (h : ∀ x : R, ‖x‖ ≤ 1 → ‖x - 1‖ ≤ 1) : IsUltrametricDist R := by
  have (x : R) (hx : ‖x‖ ≤ 1) : ‖x + 1‖ ≤ 1 := by
    simpa only [← neg_add', norm_neg] using h (-x) (norm_neg x ▸ hx)
  exact isUltrametricDist_of_forall_norm_add_one_of_norm_le_one this
lemma isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm
    (h : ∀ (x : R) (m : ℕ), ‖x + 1‖ ^ m ≤ (m + 1) • max 1 (‖x‖ ^ m)) :
    IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_norm_add_one_le_max_norm_one fun x ↦ ?_
  rw [max_comm]
  refine le_of_forall_le_of_dense fun a ha ↦ ?_
  have ha' : 1 < a := (max_lt_iff.mp ha).left
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((m + 1) : ℕ) < (a / (max 1 ‖x‖)) ^ m := by
    apply_mod_cast Real.exists_natCast_add_one_lt_pow_of_one_lt
    rwa [one_lt_div (by positivity)]
  rw [div_pow, lt_div_iff₀ (by positivity), ← nsmul_eq_mul] at hm
  have hp : max 1 ‖x‖ ^ m = max 1 (‖x‖ ^ m) := by
    rw [pow_left_monotoneOn.map_max (by simp [zero_le_one]) (norm_nonneg x), one_pow]
  rw [hp] at hm
  refine le_of_pow_le_pow_left₀ (fun h ↦ ?_) (zero_lt_one.trans ha').le ((h _ _).trans hm.le)
  simp only [h, zero_add, pow_zero, max_self, one_smul, lt_self_iff_false] at hm
lemma isUltrametricDist_of_forall_norm_natCast_le_one
    (h : ∀ n : ℕ, ‖(n : R)‖ ≤ 1) : IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm (fun x m ↦ ?_)
  replace h (x : R) (n : ℕ) : ‖n • x‖ ≤ ‖x‖ := by
    rw [nsmul_eq_mul, norm_mul]
    rcases (norm_nonneg x).eq_or_lt with hx | hx
    · simp only [← hx, mul_zero, le_refl]
    · simpa only [mul_le_iff_le_one_left hx] using h _
  transitivity ∑ k ∈ Finset.range (m + 1), ‖x‖ ^ k
  · simpa only [← norm_pow, (Commute.one_right x).add_pow, one_pow, mul_one, nsmul_eq_mul,
      Nat.cast_comm] using (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ h _ _)
  rw [← Finset.card_range (m + 1), ← Finset.sum_const, Finset.card_range]
  rcases max_cases 1 (‖x‖ ^ m) with (⟨hm, hx⟩|⟨hm, hx⟩) <;> rw [hm] <;>
  refine Finset.sum_le_sum fun i hi ↦ ?_
  · rcases eq_or_ne m 0 with rfl | hm
    · simp only [pow_zero, le_refl,
        show i = 0 by simpa only [zero_add, Finset.range_one, Finset.mem_singleton] using hi]
    · rw [pow_le_one_iff_of_nonneg (norm_nonneg _) hm] at hx
      exact pow_le_one₀ (norm_nonneg _) hx
  · refine pow_le_pow_right₀ ?_ (by simpa only [Finset.mem_range, Nat.lt_succ] using hi)
    contrapose! hx
    exact pow_le_one₀ (norm_nonneg _) hx.le
end sufficient
end IsUltrametricDist
theorem isUltrametricDist_iff_forall_norm_natCast_le_one {R : Type*}
    [NormedDivisionRing R] : IsUltrametricDist R ↔ ∀ n : ℕ, ‖(n : R)‖ ≤ 1 :=
  ⟨fun _ => IsUltrametricDist.norm_natCast_le_one R,
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one⟩