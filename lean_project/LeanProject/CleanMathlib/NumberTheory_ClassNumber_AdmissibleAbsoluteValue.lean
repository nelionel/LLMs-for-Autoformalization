import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.EuclideanAbsoluteValue
local infixl:50 " ≺ " => EuclideanDomain.r
namespace AbsoluteValue
variable {R : Type*} [EuclideanDomain R]
variable (abv : AbsoluteValue R ℤ)
structure IsAdmissible extends IsEuclidean abv where
  protected card : ℝ → ℕ
  exists_partition' :
    ∀ (n : ℕ) {ε : ℝ} (_ : 0 < ε) {b : R} (_ : b ≠ 0) (A : Fin n → R),
      ∃ t : Fin n → Fin (card ε), ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε
attribute [nolint docBlame] IsAdmissible.card
namespace IsAdmissible
variable {abv}
theorem exists_partition {ι : Type*} [Finite ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (A : ι → R) (h : abv.IsAdmissible) : ∃ t : ι → Fin (h.card ε),
      ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  obtain ⟨t, ht⟩ := h.exists_partition' n hε hb (A ∘ e.symm)
  refine ⟨t ∘ e, fun i₀ i₁ h ↦ ?_⟩
  convert (config := {transparency := .default})
    ht (e i₀) (e i₁) h <;> simp only [e.symm_apply_apply]
theorem exists_approx_aux (n : ℕ) (h : abv.IsAdmissible) :
    ∀ {ε : ℝ} (_hε : 0 < ε) {b : R} (_hb : b ≠ 0) (A : Fin (h.card ε ^ n).succ → Fin n → R),
      ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  haveI := Classical.decEq R
  induction' n with n ih
  · intro ε _hε b _hb A
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    rintro ⟨i, ⟨⟩⟩
  intro ε hε b hb A
  let M := h.card ε
  obtain ⟨s, s_inj, hs⟩ :
    ∃ s : Fin (M ^ n).succ → Fin (M ^ n.succ).succ,
      Function.Injective s ∧ ∀ i₀ i₁, (abv (A (s i₁) 0 % b - A (s i₀) 0 % b) : ℝ) < abv b • ε := by
    obtain ⟨t, ht⟩ :
      ∃ t : Fin (M ^ n.succ).succ → Fin M,
        ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ 0 % b - A i₀ 0 % b) : ℝ) < abv b • ε :=
      h.exists_partition hε hb fun x ↦ A x 0
    obtain ⟨s, hs⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := t)
        (by simpa only [Fintype.card_fin, pow_succ'] using Nat.lt_succ_self (M ^ n.succ))
    refine ⟨fun i ↦ (Finset.univ.filter fun x ↦ t x = s).toList.get <| i.castLE ?_, fun i j h ↦ ?_,
      fun i₀ i₁ ↦ ht _ _ ?_⟩
    · rwa [Finset.length_toList]
    · ext
      simpa [(Finset.nodup_toList _).getElem_inj_iff] using h
    · #adaptation_note
      have : ∀ i h, t ((Finset.univ.filter fun x ↦ t x = s).toList.get ⟨i, h⟩) = s := fun i h ↦
        (Finset.mem_filter.mp (Finset.mem_toList.mp (List.get_mem _ ⟨i, h⟩))).2
      simp only [Nat.succ_eq_add_one, Finset.length_toList, List.get_eq_getElem] at this
      simp only [Nat.succ_eq_add_one, List.get_eq_getElem, Fin.coe_castLE]
      rw [this _ (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i₁.2) hs),
        this _ (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ i₀.2) hs)]
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb fun x ↦ Fin.tail (A (s x))
  refine ⟨s k₀, s k₁, fun h ↦ hk (s_inj h), fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i⟩
  · exact hs k₀ k₁
  · exact h i
theorem exists_approx {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (h : abv.IsAdmissible) (A : Fin (h.card ε ^ Fintype.card ι).succ → ι → R) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  let e := Fintype.equivFin ι
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y ↦ A x (e.symm y)
  refine ⟨i₀, i₁, ne, fun k ↦ ?_⟩
  convert h (e k) <;> simp only [e.symm_apply_apply]
end IsAdmissible
end AbsoluteValue