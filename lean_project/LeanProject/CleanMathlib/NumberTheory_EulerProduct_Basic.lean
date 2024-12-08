import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.SmoothNumbers
lemma Summable.norm_lt_one {F : Type*} [NormedField F] [CompleteSpace F] {f : ℕ →* F}
    (hsum : Summable f) {p : ℕ} (hp : 1 < p) :
    ‖f p‖ < 1 := by
  refine summable_geometric_iff_norm_lt_one.mp ?_
  simp_rw [← map_pow]
  exact hsum.comp_injective <| Nat.pow_right_injective hp
open scoped Topology
open Nat Finset
section General
variable {R : Type*} [NormedCommRing R] {f : ℕ → R}
@[local instance] private lemma instT0Space : T0Space R := MetricSpace.instT0Space
variable [CompleteSpace R]
namespace EulerProduct
variable (hf₁ : f 1 = 1) (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
include hf₁ hmul in
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (s : Finset ℕ) :
    Summable (fun m : factoredNumbers s ↦ ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s ↦ f m)
        (∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n)) := by
  induction' s using Finset.induction with p s hp ih
  · rw [factoredNumbers_empty]
    simp only [not_mem_empty, IsEmpty.forall_iff, forall_const, filter_true_of_mem, prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  · rw [filter_insert]
    split_ifs with hpp
    · constructor
      · simp only [← (equivProdNatFactoredNumbers hpp hp).summable_iff, Function.comp_def,
          equivProdNatFactoredNumbers_apply', factoredNumbers.map_prime_pow_mul hmul hpp hp]
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_mul_le ..) ?_
        apply Summable.mul_of_nonneg (hsum hpp) ih.1 <;> exact fun n ↦ norm_nonneg _
      · have hp' : p ∉ {p ∈ s | p.Prime} := mt (mem_of_mem_filter p) hp
        rw [prod_insert hp', ← (equivProdNatFactoredNumbers hpp hp).hasSum_iff, Function.comp_def]
        conv =>
          enter [1, x]
          rw [equivProdNatFactoredNumbers_apply', factoredNumbers.map_prime_pow_mul hmul hpp hp]
        have : T3Space R := instT3Space 
        apply (hsum hpp).of_norm.hasSum.mul ih.2
        apply summable_mul_of_summable_norm (hsum hpp) ih.1
    · rwa [factoredNumbers_insert s hpp]
include hf₁ hmul in
lemma prod_filter_prime_tsum_eq_tsum_factoredNumbers (hsum : Summable (‖f ·‖)) (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n) = ∑' m : factoredNumbers s, f m :=
  (summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm
lemma norm_tsum_factoredNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε : ℝ}
    (εpos : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, primesBelow N ≤ s →
      ‖(∑' m : ℕ, f m) - ∑' m : factoredNumbers s, f m‖ < ε := by
  obtain ⟨N, hN⟩ :=
    summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) <| Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN
  refine ⟨N, fun s hs ↦ ?_⟩
  have := hN _ <| factoredNumbers_compl hs
  rwa [← tsum_subtype_add_tsum_subtype_compl hsum (factoredNumbers s),
    add_sub_cancel_left, tsum_eq_tsum_diff_singleton (factoredNumbers s)ᶜ hf₀]
include hf₁ hmul in
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p ∈ N.primesBelow, ∑' n : ℕ, f (p ^ n)) := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul hsum _
include hf₁ hmul in
lemma prod_primesBelow_tsum_eq_tsum_smoothNumbers (hsum : Summable (‖f ·‖)) (N : ℕ) :
    ∏ p ∈ N.primesBelow, ∑' n : ℕ, f (p ^ n) = ∑' m : N.smoothNumbers, f m :=
  (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm
lemma norm_tsum_smoothNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖(∑' m : ℕ, f m) - ∑' m : N.smoothNumbers, f m‖ < ε := by
  conv => enter [1, N₀, N]; rw [smoothNumbers_eq_factoredNumbers]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum hf₀ εpos
  refine ⟨N₀, fun N hN ↦ hN₀ (range N) fun p hp ↦ ?_⟩
  exact mem_range.mpr <| (lt_of_mem_primesBelow hp).trans_le hN
include hf₁ hmul in
theorem eulerProduct_hasProd (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (fun p : Primes ↦ ∑' e, f (p ^ e)) (∑' n, f n) := by
  let F : ℕ → R := fun n ↦ ∑' e, f (n ^ e)
  change HasProd (F ∘ Subtype.val) _
  rw [hasProd_subtype_iff_mulIndicator,
    show Set.mulIndicator (fun p : ℕ ↦ Irreducible p) =  {p | Nat.Prime p}.mulIndicator from rfl,
    HasProd, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum.of_norm hf₀ hε
  refine ⟨range N₀, fun s hs ↦ ?_⟩
  have : ∏ p ∈ s, {p | Nat.Prime p}.mulIndicator F p = ∏ p ∈ s with p.Prime, F p :=
    prod_mulIndicator_eq_prod_filter s (fun _ ↦ F) _ id
  rw [this, dist_eq_norm, prod_filter_prime_tsum_eq_tsum_factoredNumbers hf₁ hmul hsum,
    norm_sub_rev]
  exact hN₀ s fun p hp ↦ hs <| mem_range.mpr <| lt_of_mem_primesBelow hp
include hf₁ hmul in
theorem eulerProduct_hasProd_mulIndicator (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (Set.mulIndicator {p | Nat.Prime p} fun p ↦  ∑' e, f (p ^ e)) (∑' n, f n) := by
  rw [← hasProd_subtype_iff_mulIndicator]
  exact eulerProduct_hasProd hf₁ hmul hsum hf₀
open Filter in
include hf₁ hmul in
theorem eulerProduct (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  have := (eulerProduct_hasProd_mulIndicator hf₁ hmul hsum hf₀).tendsto_prod_nat
  let F : ℕ → R := fun p ↦ ∑' (e : ℕ), f (p ^ e)
  have H (n : ℕ) : ∏ i ∈ range n, Set.mulIndicator {p | Nat.Prime p} F i =
                     ∏ p ∈ primesBelow n, ∑' (e : ℕ), f (p ^ e) :=
    prod_mulIndicator_eq_prod_filter (range n) (fun _ ↦ F) (fun _ ↦ {p | Nat.Prime p}) id
  simpa only [H]
include hf₁ hmul in
theorem eulerProduct_tprod (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  (eulerProduct_hasProd hf₁ hmul hsum hf₀).tprod_eq
end EulerProduct
namespace ArithmeticFunction
open EulerProduct
nonrec theorem IsMultiplicative.eulerProduct_hasProd {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ ∑' e, f (p ^ e)) (∑' n, f n) :=
  eulerProduct_hasProd hf.1 hf.2 hsum f.map_zero
open Filter in
nonrec theorem IsMultiplicative.eulerProduct {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) :=
  eulerProduct hf.1 hf.2 hsum f.map_zero
nonrec theorem IsMultiplicative.eulerProduct_tprod {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  eulerProduct_tprod hf.1 hf.2 hsum f.map_zero
end ArithmeticFunction
end General
section CompletelyMultiplicative
variable {F : Type*} [NormedField F] [CompleteSpace F]
namespace EulerProduct
lemma one_sub_inv_eq_geometric_of_summable_norm {f : ℕ →*₀ F} {p : ℕ} (hp : p.Prime)
    (hsum : Summable fun x ↦ ‖f x‖) :
    (1 - f p)⁻¹ = ∑' (e : ℕ), f (p ^ e) := by
  simp only [map_pow]
  refine (tsum_geometric_of_norm_lt_one <| summable_geometric_iff_norm_lt_one.mp ?_).symm
  refine Summable.of_norm ?_
  simpa only [Function.comp_def, map_pow]
    using hsum.comp_injective <| Nat.pow_right_injective hp.one_lt
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (s : Finset ℕ) :
    Summable (fun m : factoredNumbers s ↦ ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s ↦ f m) (∏ p ∈ s with p.Prime, (1 - f p)⁻¹) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have H₁ :
      ∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n) = ∏ p ∈ s with p.Prime, (1 - f p)⁻¹ := by
    refine prod_congr rfl fun p hp ↦ ?_
    simp only [map_pow]
    exact tsum_geometric_of_norm_lt_one <| h (mem_filter.mp hp).2
  have H₂ : ∀ {p : ℕ}, p.Prime → Summable fun n ↦ ‖f (p ^ n)‖ := by
    intro p hp
    simp only [map_pow]
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_pow_le ..) ?_
    exact summable_geometric_iff_norm_lt_one.mpr <| (norm_norm (f p)).symm ▸ h hp
  exact H₁ ▸ summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum f.map_one hmul H₂ s
lemma prod_filter_prime_geometric_eq_tsum_factoredNumbers {f : ℕ →* F} (hsum : Summable f)
    (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, (1 - f p)⁻¹ = ∑' m : factoredNumbers s, f m := by
  refine (summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric ?_ s).2.tsum_eq.symm
  exact fun {_} hp ↦ hsum.norm_lt_one hp.one_lt
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p ∈ N.primesBelow, (1 - f p)⁻¹) := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric h _
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : ℕ →* F} (hsum : Summable f) (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumbers, f m := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum _
theorem eulerProduct_completely_multiplicative_hasProd {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ (1 - f p)⁻¹) (∑' n, f n) := by
  have H : (fun p : Primes ↦ (1 - f p)⁻¹) = fun p : Primes ↦ ∑' (e : ℕ), f (p ^ e) :=
    funext <| fun p ↦ one_sub_inv_eq_geometric_of_summable_norm p.prop hsum
  simpa only [map_pow, H]
    using eulerProduct_hasProd f.map_one (fun {m n} _ ↦ f.map_mul m n) hsum f.map_zero
theorem eulerProduct_completely_multiplicative_tprod {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, (1 - f p)⁻¹ = ∑' n, f n :=
  (eulerProduct_completely_multiplicative_hasProd hsum).tprod_eq
open Filter in
theorem eulerProduct_completely_multiplicative {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑' n, f n)) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have := (eulerProduct_hasProd_mulIndicator f.map_one hmul hsum f.map_zero).tendsto_prod_nat
  have H (n : ℕ) : ∏ p ∈ range n, {p | Nat.Prime p}.mulIndicator (fun p ↦ (1 - f p)⁻¹) p =
                     ∏ p ∈ primesBelow n, (1 - f p)⁻¹ :=
    prod_mulIndicator_eq_prod_filter
      (range n) (fun _ ↦ fun p ↦ (1 - f p)⁻¹) (fun _ ↦ {p | Nat.Prime p}) id
  have H' : {p | Nat.Prime p}.mulIndicator (fun p ↦ (1 - f p)⁻¹) =
              {p | Nat.Prime p}.mulIndicator (fun p ↦ ∑' e : ℕ, f (p ^ e)) :=
    Set.mulIndicator_congr fun p hp ↦ one_sub_inv_eq_geometric_of_summable_norm hp hsum
  simpa only [← H, H'] using this
end EulerProduct
end CompletelyMultiplicative