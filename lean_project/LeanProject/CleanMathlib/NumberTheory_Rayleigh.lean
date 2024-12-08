import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.Real.Irrational
noncomputable def beattySeq (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌊k * r⌋
noncomputable def beattySeq' (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌈k * r⌉ - 1
namespace Beatty
variable {r s : ℝ} {j : ℤ}
private theorem no_collision (hrs : r.IsConjExponent s) :
    Disjoint {beattySeq r k | k} {beattySeq' s k | k} := by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  rw [beattySeq, Int.floor_eq_iff, ← div_le_iff₀ hrs.pos, ← lt_div_iff₀ hrs.pos] at h₁
  rw [beattySeq', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel_right, ← div_lt_iff₀ hrs.symm.pos, ← le_div_iff₀ hrs.symm.pos] at h₂
  have h₃ := add_lt_add_of_le_of_lt h₁.1 h₂.1
  have h₄ := add_lt_add_of_lt_of_le h₁.2 h₂.2
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_conj, one_mul] at h₃ h₄
  rw [← Int.cast_one] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_lt h₃
private theorem no_anticollision (hrs : r.IsConjExponent s) :
    ¬∃ j k m : ℤ, k < j / r ∧ (j + 1) / r ≤ k + 1 ∧ m ≤ j / s ∧ (j + 1) / s < m + 1 := by
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₃ := add_lt_add_of_lt_of_le h₁₁ h₂₁
  have h₄ := add_lt_add_of_le_of_lt h₁₂ h₂₂
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_conj, one_mul] at h₃ h₄
  rw [← Int.cast_one, ← add_assoc, add_lt_add_iff_right, add_right_comm] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_lt h₃
private theorem hit_or_miss (h : r > 0) :
    j ∈ {beattySeq r k | k} ∨ ∃ k : ℤ, k < j / r ∧ (j + 1) / r ≤ k + 1 := by
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [Int.cast_sub, Int.cast_one, lt_div_iff₀ h, sub_add_cancel]
    exact ⟨‹_›, Int.le_ceil _⟩
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySeq, Int.floor_eq_iff, Int.cast_sub, Int.cast_one, ← lt_div_iff₀ h, sub_lt_iff_lt_add]
    exact ⟨‹_›, Int.ceil_lt_add_one _⟩
private theorem hit_or_miss' (h : r > 0) :
    j ∈ {beattySeq' r k | k} ∨ ∃ k : ℤ, k ≤ j / r ∧ (j + 1) / r < k + 1 := by
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · exact Or.inr ⟨⌊(j + 1) / r⌋, (le_div_iff₀ h).2 ‹_›, Int.lt_floor_add_one _⟩
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySeq', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one]
    constructor
    · rwa [add_sub_cancel_right]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : ℝ) h)
end Beatty
theorem compl_beattySeq {r s : ℝ} (hrs : r.IsConjExponent s) :
    {beattySeq r k | k}ᶜ = {beattySeq' s k | k} := by
  ext j
  by_cases h₁ : j ∈ {beattySeq r k | k} <;> by_cases h₂ : j ∈ {beattySeq' s k | k}
  · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hrs)).elim
  · simp only [Set.mem_compl_iff, h₁, h₂, not_true_eq_false]
  · simp only [Set.mem_compl_iff, h₁, h₂, not_false_eq_true]
  · have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hrs.pos).resolve_left h₁
    have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hrs.symm.pos).resolve_left h₂
    exact (Beatty.no_anticollision hrs ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim
theorem compl_beattySeq' {r s : ℝ} (hrs : r.IsConjExponent s) :
    {beattySeq' r k | k}ᶜ = {beattySeq s k | k} := by
  rw [← compl_beattySeq hrs.symm, compl_compl]
open scoped symmDiff
theorem beattySeq_symmDiff_beattySeq'_pos {r s : ℝ} (hrs : r.IsConjExponent s) :
    {beattySeq r k | k > 0} ∆ {beattySeq' s k | k > 0} = {n | 0 < n} := by
  apply Set.eq_of_subset_of_subset
  · rintro j (⟨⟨k, hk, hjk⟩, -⟩ | ⟨⟨k, hk, hjk⟩, -⟩)
    · rw [Set.mem_setOf_eq, ← hjk, beattySeq, Int.floor_pos]
      exact one_le_mul_of_one_le_of_one_le (by norm_cast) hrs.one_lt.le
    · rw [Set.mem_setOf_eq, ← hjk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one]
      exact one_lt_mul_of_le_of_lt (by norm_cast) hrs.symm.one_lt
  intro j (hj : 0 < j)
  have hb₁ : ∀ s ≥ 0, j ∈ {beattySeq s k | k > 0} ↔ j ∈ {beattySeq s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySeq, Int.floor_pos] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans_le hj) hs
  have hb₂ : ∀ s ≥ 0, j ∈ {beattySeq' s k | k > 0} ↔ j ∈ {beattySeq' s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans hj) hs
  rw [Set.mem_symmDiff, hb₁ _ hrs.nonneg, hb₂ _ hrs.symm.nonneg, ← compl_beattySeq hrs,
    Set.not_mem_compl_iff, Set.mem_compl_iff, and_self, and_self]
  exact or_not
theorem beattySeq'_symmDiff_beattySeq_pos {r s : ℝ} (hrs : r.IsConjExponent s) :
    {beattySeq' r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [symmDiff_comm, beattySeq_symmDiff_beattySeq'_pos hrs.symm]
theorem Irrational.beattySeq'_pos_eq {r : ℝ} (hr : Irrational r) :
    {beattySeq' r k | k > 0} = {beattySeq r k | k > 0} := by
  dsimp only [beattySeq, beattySeq']
  congr! 4; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
  rw [sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel_right]
  refine ⟨(Int.floor_le _).lt_of_ne fun h ↦ ?_, (Int.lt_floor_add_one _).le⟩
  exact (hr.int_mul hk.ne').ne_int ⌊k * r⌋ h.symm
theorem Irrational.beattySeq_symmDiff_beattySeq_pos {r s : ℝ}
    (hrs : r.IsConjExponent s) (hr : Irrational r) :
    {beattySeq r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [← hr.beattySeq'_pos_eq, beattySeq'_symmDiff_beattySeq_pos hrs]