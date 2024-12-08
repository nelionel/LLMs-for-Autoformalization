import Mathlib.Combinatorics.SimpleGraph.Regularity.Increment
open Finpartition Finset Fintype Function SzemerediRegularity
variable {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ}
  {l : ℕ}
theorem szemeredi_regularity (hε : 0 < ε) (hl : l ≤ card α) :
    ∃ P : Finpartition univ,
      P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ bound ε l ∧ P.IsUniform G ε := by
  obtain hα | hα := le_total (card α) (bound ε l)
  · refine ⟨⊥, bot_isEquipartition _, ?_⟩
    rw [card_bot, card_univ]
    exact ⟨hl, hα, bot_isUniform _ hε⟩
  let t := initialBound ε l
  have htα : t ≤ #(univ : Finset α) :=
    (initialBound_le_bound _ _).trans (by rwa [Finset.card_univ])
  obtain ⟨dum, hdum₁, hdum₂⟩ :=
    exists_equipartition_card_eq (univ : Finset α) (initialBound_pos _ _).ne' htα
  obtain hε₁ | hε₁ := le_total 1 ε
  · exact ⟨dum, hdum₁, (le_initialBound ε l).trans hdum₂.ge,
      hdum₂.le.trans (initialBound_le_bound ε l), (dum.isUniform_one G).mono hε₁⟩
  have : Nonempty α := by
    rw [← Fintype.card_pos_iff]
    exact (bound_pos _ _).trans_le hα
  suffices h : ∀ i, ∃ P : Finpartition (univ : Finset α), P.IsEquipartition ∧ t ≤ #P.parts ∧
    #P.parts ≤ stepBound^[i] t ∧ (P.IsUniform G ε ∨ ε ^ 5 / 4 * i ≤ P.energy G) by
    obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := h (⌊4 / ε ^ 5⌋₊ + 1)
    refine ⟨P, hP₁, (le_initialBound _ _).trans hP₂, hP₃.trans ?_,
      hP₄.resolve_right fun hPenergy => lt_irrefl (1 : ℝ) ?_⟩
    · rw [iterate_succ_apply', stepBound, bound]
      gcongr
      norm_num
    calc
      (1 : ℝ) = ε ^ 5 / ↑4 * (↑4 / ε ^ 5) := by
        rw [mul_comm, div_mul_div_cancel₀ (pow_pos hε 5).ne']; norm_num
      _ < ε ^ 5 / 4 * (⌊4 / ε ^ 5⌋₊ + 1) :=
        ((mul_lt_mul_left <| by positivity).2 (Nat.lt_floor_add_one _))
      _ ≤ (P.energy G : ℝ) := by rwa [← Nat.cast_add_one]
      _ ≤ 1 := mod_cast P.energy_le_one G
  intro i
  induction' i with i ih
  · refine ⟨dum, hdum₁, hdum₂.ge, hdum₂.le, Or.inr ?_⟩
    rw [Nat.cast_zero, mul_zero]
    exact mod_cast dum.energy_nonneg G
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := ih
  by_cases huniform : P.IsUniform G ε
  · refine ⟨P, hP₁, hP₂, ?_, Or.inl huniform⟩
    rw [iterate_succ_apply']
    exact hP₃.trans (le_stepBound _)
  replace hP₄ := hP₄.resolve_left huniform
  have hεl' : 100 ≤ 4 ^ #P.parts * ε ^ 5 :=
    (hundred_lt_pow_initialBound_mul hε l).le.trans
      (mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hP₂) <| by positivity)
  have hi : (i : ℝ) ≤ 4 / ε ^ 5 := by
    have hi : ε ^ 5 / 4 * ↑i ≤ 1 := hP₄.trans (mod_cast P.energy_le_one G)
    rw [div_mul_eq_mul_div, div_le_iff₀ (show (0 : ℝ) < 4 by norm_num)] at hi
    norm_num at hi
    rwa [le_div_iff₀' (pow_pos hε _)]
  have hsize : #P.parts ≤ stepBound^[⌊4 / ε ^ 5⌋₊] t :=
    hP₃.trans (monotone_iterate_of_id_le le_stepBound (Nat.le_floor hi) _)
  have hPα : #P.parts * 16 ^ #P.parts ≤ card α :=
    (Nat.mul_le_mul hsize (Nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hα
  refine ⟨increment hP₁ G ε, increment_isEquipartition hP₁ G ε, ?_, ?_, Or.inr <| le_trans ?_ <|
    energy_increment hP₁ ((seven_le_initialBound ε l).trans hP₂) hεl' hPα huniform hε.le hε₁⟩
  · rw [card_increment hPα huniform]
    exact hP₂.trans (le_stepBound _)
  · rw [card_increment hPα huniform, iterate_succ_apply']
    exact stepBound_mono hP₃
  · rw [Nat.cast_succ, mul_add, mul_one]
    exact add_le_add_right hP₄ _