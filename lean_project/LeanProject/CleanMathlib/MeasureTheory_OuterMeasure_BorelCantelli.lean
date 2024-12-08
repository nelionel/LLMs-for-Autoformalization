import Mathlib.MeasureTheory.OuterMeasure.AE
open Filter Set
open scoped ENNReal Topology
namespace MeasureTheory
variable {α ι F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] [Countable ι] {μ : F}
theorem measure_limsup_cofinite_eq_zero {s : ι → Set α} (hs : ∑' i, μ (s i) ≠ ∞) :
    μ (limsup s cofinite) = 0 := by
  refine bot_unique <| ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun t ↦ ?_
  calc
    μ (limsup s cofinite) ≤ μ (⋃ i : {i // i ∉ t}, s i) := by
      gcongr
      rw [hasBasis_cofinite.limsup_eq_iInf_iSup, iUnion_subtype]
      exact iInter₂_subset _ t.finite_toSet
    _ ≤ ∑' i : {i // i ∉ t}, μ (s i) := measure_iUnion_le _
theorem measure_limsup_atTop_eq_zero {s : ℕ → Set α} (hs : ∑' i, μ (s i) ≠ ∞) :
    μ (limsup s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop, measure_limsup_cofinite_eq_zero hs]
@[deprecated (since := "2024-09-01")]
alias measure_limsup_eq_zero := measure_limsup_atTop_eq_zero
theorem ae_finite_setOf_mem {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    ∀ᵐ x ∂μ, {i | x ∈ s i}.Finite := by
  rw [ae_iff, ← measure_limsup_cofinite_eq_zero h]
  congr 1 with x
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]
theorem measure_setOf_frequently_eq_zero {p : ℕ → α → Prop} (hp : ∑' i, μ { x | p i x } ≠ ∞) :
    μ { x | ∃ᶠ n in atTop, p n x } = 0 := by
  simpa only [limsup_eq_iInf_iSup_of_nat, frequently_atTop, ← bex_def, setOf_forall,
    setOf_exists] using measure_limsup_atTop_eq_zero hp
theorem ae_eventually_not_mem {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n :=
  measure_setOf_frequently_eq_zero hs
theorem measure_liminf_cofinite_eq_zero [Infinite ι]  {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    μ (liminf s cofinite) = 0 := by
  rw [← le_zero_iff, ← measure_limsup_cofinite_eq_zero h]
  exact measure_mono liminf_le_limsup
theorem measure_liminf_atTop_eq_zero {s : ℕ → Set α} (h : (∑' i, μ (s i)) ≠ ∞) :
    μ (liminf s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop, measure_liminf_cofinite_eq_zero h]
theorem limsup_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : limsup (α := Set α) s atTop =ᵐ[μ] t := by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
  refine eventuallyEq_set.2 <| h.mono fun x hx ↦ ?_
  simp [mem_limsup_iff_frequently_mem, hx]
theorem liminf_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : liminf (α := Set α) s atTop =ᵐ[μ] t := by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
  refine eventuallyEq_set.2 <| h.mono fun x hx ↦ ?_
  simp only [mem_liminf_iff_eventually_mem, hx, eventually_const]
end MeasureTheory