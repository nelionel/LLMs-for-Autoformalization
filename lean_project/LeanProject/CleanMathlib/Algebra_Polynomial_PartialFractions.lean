import Mathlib.Algebra.Polynomial.Div
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
variable (R : Type) [CommRing R] [IsDomain R]
open Polynomial
variable (K : Type) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]
section TwoDenominators
open algebraMap
theorem div_eq_quo_add_rem_div_add_rem_div (f : R[X]) {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂) :
    ∃ q r₁ r₂ : R[X],
      r₁.degree < g₁.degree ∧
        r₂.degree < g₂.degree ∧ (f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ := by
  rcases hcoprime with ⟨c, d, hcd⟩
  refine
    ⟨f * d /ₘ g₁ + f * c /ₘ g₂, f * d %ₘ g₁, f * c %ₘ g₂, degree_modByMonic_lt _ hg₁,
      degree_modByMonic_lt _ hg₂, ?_⟩
  have hg₁' : (↑g₁ : K) ≠ 0 := by
    norm_cast
    exact hg₁.ne_zero
  have hg₂' : (↑g₂ : K) ≠ 0 := by
    norm_cast
    exact hg₂.ne_zero
  have hfc := modByMonic_add_div (f * c) hg₂
  have hfd := modByMonic_add_div (f * d) hg₁
  field_simp
  norm_cast
  linear_combination -1 * f * hcd + -1 * g₁ * hfc + -1 * g₂ * hfd
end TwoDenominators
section NDenominators
open algebraMap
theorem div_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
        ((↑f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K) := by
  classical
  induction' s using Finset.induction_on with a b hab Hind f generalizing f
  · refine ⟨f, fun _ : ι => (0 : R[X]), fun i => ?_, by simp⟩
    rintro ⟨⟩
  obtain ⟨q₀, r₁, r₂, hdeg₁, _, hf : (↑f : K) / _ = _⟩ :=
    div_eq_quo_add_rem_div_add_rem_div R K f
      (hg a (b.mem_insert_self a) : Monic (g a))
      (monic_prod_of_monic _ _ fun i hi => hg i (Finset.mem_insert_of_mem hi) :
        Monic (∏ i ∈ b, g i))
      (IsCoprime.prod_right fun i hi =>
        hcop (Finset.mem_coe.2 (b.mem_insert_self a))
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) (by rintro rfl; exact hab hi))
  obtain ⟨q, r, hrdeg, IH⟩ :=
    Hind _ (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (Set.Pairwise.mono (Finset.coe_subset.2 fun i hi => Finset.mem_insert_of_mem hi) hcop)
  refine ⟨q₀ + q, fun i => if i = a then r₁ else r i, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h1
    · cases h1
      intro
      exact hdeg₁
    · intro hi
      exact hrdeg i (Finset.mem_of_mem_insert_of_ne hi h1)
  norm_cast at hf IH ⊢
  rw [Finset.prod_insert hab, hf, IH, Finset.sum_insert hab, if_pos rfl]
  trans (↑(q₀ + q : R[X]) : K) + (↑r₁ / ↑(g a) + ∑ i ∈ b, (r i : K) / (g i : K))
  · push_cast
    ring
  congr 2
  refine Finset.sum_congr rfl fun x hxb => ?_
  rw [if_neg]
  rintro rfl
  exact hab hxb
end NDenominators