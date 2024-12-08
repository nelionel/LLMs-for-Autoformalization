import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Filter Topology
namespace Real
section LowerSequence
noncomputable def eulerMascheroniSeq (n : ℕ) : ℝ := harmonic n - log (n + 1)
lemma eulerMascheroniSeq_zero : eulerMascheroniSeq 0 = 0 := by
  simp [eulerMascheroniSeq, harmonic_zero]
lemma strictMono_eulerMascheroniSeq : StrictMono eulerMascheroniSeq := by
  refine strictMono_nat_of_lt_succ (fun n ↦ ?_)
  rw [eulerMascheroniSeq, eulerMascheroniSeq, ← sub_pos, sub_sub_sub_comm,
    harmonic_succ, add_comm, Rat.cast_add, add_sub_cancel_right,
    ← log_div (by positivity) (by positivity), add_div, Nat.cast_add_one,
    Nat.cast_add_one, div_self (by positivity), sub_pos, one_div, Rat.cast_inv, Rat.cast_add,
    Rat.cast_one, Rat.cast_natCast]
  refine (log_lt_sub_one_of_pos ?_ (ne_of_gt <| lt_add_of_pos_right _ ?_)).trans_le (le_of_eq ?_)
  · positivity
  · positivity
  · simp only [add_sub_cancel_left]
lemma one_half_lt_eulerMascheroniSeq_six : 1 / 2 < eulerMascheroniSeq 6 := by
  have : eulerMascheroniSeq 6 = 49 / 20 - log 7 := by
    rw [eulerMascheroniSeq]
    norm_num
  rw [this, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', log_lt_iff_lt_exp (by positivity)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num
end LowerSequence
section UpperSequence
noncomputable def eulerMascheroniSeq' (n : ℕ) : ℝ :=
  if n = 0 then 2 else ↑(harmonic n) - log n
lemma eulerMascheroniSeq'_one : eulerMascheroniSeq' 1 = 1 := by
  simp [eulerMascheroniSeq']
lemma strictAnti_eulerMascheroniSeq' : StrictAnti eulerMascheroniSeq' := by
  refine strictAnti_nat_of_succ_lt (fun n ↦ ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerMascheroniSeq']
  simp_rw [eulerMascheroniSeq', eq_false_intro hn.ne', reduceCtorEq, if_false]
  rw [← sub_pos, sub_sub_sub_comm,
    harmonic_succ, Rat.cast_add, ← sub_sub, sub_self, zero_sub, sub_eq_add_neg, neg_sub,
    ← sub_eq_neg_add, sub_pos, ← log_div (by positivity) (by positivity), ← neg_lt_neg_iff,
    ← log_inv]
  refine (log_lt_sub_one_of_pos ?_ ?_).trans_le (le_of_eq ?_)
  · positivity
  · field_simp
  · field_simp
lemma eulerMascheroniSeq'_six_lt_two_thirds : eulerMascheroniSeq' 6 < 2 / 3 := by
  have h1 : eulerMascheroniSeq' 6 = 49 / 20 - log 6 := by
    rw [eulerMascheroniSeq']
    norm_num
  rw [h1, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_log_iff_exp_lt (by positivity)]
  norm_num
  have := rpow_lt_rpow (exp_pos _).le exp_one_lt_d9 (by norm_num : (0 : ℝ) < 107 / 60)
  rw [exp_one_rpow] at this
  refine lt_trans this ?_
  rw [← rpow_lt_rpow_iff (z := 60), ← rpow_mul, div_mul_cancel₀, ← Nat.cast_ofNat,
    ← Nat.cast_ofNat, rpow_natCast, Nat.cast_ofNat, ← Nat.cast_ofNat (n := 60), rpow_natCast]
  · norm_num
  all_goals positivity
lemma eulerMascheroniSeq_lt_eulerMascheroniSeq' (m n : ℕ) :
    eulerMascheroniSeq m < eulerMascheroniSeq' n := by
  have (r : ℕ) : eulerMascheroniSeq r < eulerMascheroniSeq' r := by
    rcases eq_zero_or_pos r with rfl | hr
    · simp [eulerMascheroniSeq, eulerMascheroniSeq']
    simp only [eulerMascheroniSeq, eulerMascheroniSeq', hr.ne', if_false]
    gcongr
    linarith
  apply (strictMono_eulerMascheroniSeq.monotone (le_max_left m n)).trans_lt
  exact (this _).trans_le (strictAnti_eulerMascheroniSeq'.antitone (le_max_right m n))
end UpperSequence
noncomputable def eulerMascheroniConstant : ℝ := limUnder atTop eulerMascheroniSeq
lemma tendsto_eulerMascheroniSeq :
    Tendsto eulerMascheroniSeq atTop (𝓝 eulerMascheroniConstant) := by
  have := tendsto_atTop_ciSup strictMono_eulerMascheroniSeq.monotone ?_
  · rwa [eulerMascheroniConstant, this.limUnder_eq]
  · exact ⟨_, fun _ ⟨_, hn⟩ ↦ hn ▸ (eulerMascheroniSeq_lt_eulerMascheroniSeq' _ 1).le⟩
lemma tendsto_harmonic_sub_log_add_one :
    Tendsto (fun n : ℕ ↦ harmonic n - log (n + 1)) atTop (𝓝 eulerMascheroniConstant) :=
  tendsto_eulerMascheroniSeq
lemma tendsto_eulerMascheroniSeq' :
    Tendsto eulerMascheroniSeq' atTop (𝓝 eulerMascheroniConstant) := by
  suffices Tendsto (fun n ↦ eulerMascheroniSeq' n - eulerMascheroniSeq n) atTop (𝓝 0) by
    simpa using this.add tendsto_eulerMascheroniSeq
  suffices Tendsto (fun x : ℝ ↦ log (x + 1) - log x) atTop (𝓝 0) by
    apply (this.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [eulerMascheroniSeq, eulerMascheroniSeq', eq_false_intro hn]
  suffices Tendsto (fun x : ℝ ↦ log (1 + 1 / x)) atTop (𝓝 0) by
    apply this.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← log_div (by positivity) (by positivity), add_div, div_self hx.ne']
  simpa only [add_zero, log_one] using
    ((tendsto_const_nhds.div_atTop tendsto_id).const_add 1).log (by positivity)
lemma tendsto_harmonic_sub_log :
    Tendsto (fun n : ℕ ↦ harmonic n - log n) atTop (𝓝 eulerMascheroniConstant) := by
  apply tendsto_eulerMascheroniSeq'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp_rw [eulerMascheroniSeq', hn, if_false]
lemma eulerMascheroniSeq_lt_eulerMascheroniConstant (n : ℕ) :
    eulerMascheroniSeq n < eulerMascheroniConstant := by
  refine (strictMono_eulerMascheroniSeq (Nat.lt_succ_self n)).trans_le ?_
  apply strictMono_eulerMascheroniSeq.monotone.ge_of_tendsto tendsto_eulerMascheroniSeq
lemma eulerMascheroniConstant_lt_eulerMascheroniSeq' (n : ℕ) :
    eulerMascheroniConstant < eulerMascheroniSeq' n := by
  refine lt_of_le_of_lt ?_ (strictAnti_eulerMascheroniSeq' (Nat.lt_succ_self n))
  apply strictAnti_eulerMascheroniSeq'.antitone.le_of_tendsto tendsto_eulerMascheroniSeq'
lemma one_half_lt_eulerMascheroniConstant : 1 / 2 < eulerMascheroniConstant :=
  one_half_lt_eulerMascheroniSeq_six.trans (eulerMascheroniSeq_lt_eulerMascheroniConstant _)
lemma eulerMascheroniConstant_lt_two_thirds : eulerMascheroniConstant < 2 / 3 :=
  (eulerMascheroniConstant_lt_eulerMascheroniSeq' _).trans eulerMascheroniSeq'_six_lt_two_thirds
end Real