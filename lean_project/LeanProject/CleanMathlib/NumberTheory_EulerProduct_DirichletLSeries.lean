import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Dirichlet
open Complex
variable {s : ℂ}
noncomputable
def riemannZetaSummandHom (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _
noncomputable
def dirichletSummandHom {n : ℕ} (χ : DirichletCharacter ℂ n) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := χ n * (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..
lemma summable_riemannZetaSummand (hs : 1 < s.re) :
    Summable (fun n ↦ ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert Real.summable_nat_rpow_inv.mpr hs with n
  rw [← ofReal_natCast, Complex.norm_eq_abs,
    abs_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) <| re_neg_ne_zero_of_one_lt_re hs,
    neg_re, Real.rpow_neg <| Nat.cast_nonneg n]
lemma tsum_riemannZetaSummand (hs : 1 < s.re) :
    ∑' (n : ℕ), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n = riemannZeta s := by
  have hsum := summable_riemannZetaSummand hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, tsum_eq_zero_add hsum.of_norm, map_zero, zero_add]
  simp only [riemannZetaSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Nat.cast_add, Nat.cast_one, one_div]
lemma summable_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    Summable (fun n ↦ ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ by positivity)
    (fun n ↦ mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)
open scoped LSeries.notation in
lemma tsum_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    ∑' (n : ℕ), dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n = L ↗χ s := by
  simp only [dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]
open Filter Nat Topology EulerProduct
theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative_hasProd <| summable_riemannZetaSummand hs
theorem riemannZeta_eulerProduct_tprod (hs : 1 < s.re) :
    ∏' p : Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  (riemannZeta_eulerProduct_hasProd hs).tprod_eq
theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (riemannZeta s)) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative <| summable_riemannZetaSummand hs
open scoped LSeries.notation
theorem DirichletCharacter.LSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (L ↗χ s) := by
  rw [← tsum_dirichletSummand χ hs]
  convert eulerProduct_completely_multiplicative_hasProd <| summable_dirichletSummand χ hs
@[deprecated (since := "2024-11-14")] alias
  dirichletLSeries_eulerProduct_hasProd := DirichletCharacter.LSeries_eulerProduct_hasProd
theorem DirichletCharacter.LSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    ∏' p : Primes, (1 - χ p * (p : ℂ) ^ (-s))⁻¹ = L ↗χ s :=
  (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq
@[deprecated (since := "2024-11-14")] alias
  dirichlet_LSeries_eulerProduct_tprod := DirichletCharacter.LSeries_eulerProduct_tprod
theorem DirichletCharacter.LSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (L ↗χ s)) := by
  rw [← tsum_dirichletSummand χ hs]
  apply eulerProduct_completely_multiplicative <| summable_dirichletSummand χ hs
@[deprecated (since := "2024-11-14")] alias
  dirichletLSeries_eulerProduct := DirichletCharacter.LSeries_eulerProduct
open LSeries
theorem DirichletCharacter.LSeries_eulerProduct_exp_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  let f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, f]
  simpa only [LSeries, h]
    using exp_tsum_primes_log_eq_tsum (f := f) <| summable_dirichletSummand χ hs
open DirichletCharacter
theorem ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert modOne_eq_one (R := ℂ) ▸
    DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter ℂ 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]
theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs
lemma DirichletCharacter.LSeries_changeLevel {M N : ℕ} [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(changeLevel hMN χ) s =
      LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rw [prod_eq_tprod_mulIndicator, ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]
  have (f : Primes → ℂ) : ∏' (p : Primes), f p = ∏' (p : ↑{p : ℕ | p.Prime}), f p := rfl
  rw [this, tprod_subtype _ fun p : ℕ ↦ (1 - (changeLevel hMN χ) p * p ^ (-s))⁻¹,
    this, tprod_subtype _ fun p : ℕ ↦ (1 - χ p * p ^ (-s))⁻¹, ← tprod_mul]
  rotate_left 
  · exact multipliable_subtype_iff_mulIndicator.mp
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  · exact multipliable_subtype_iff_mulIndicator.mp Multipliable.of_finite
  · congr 1 with p
    simp only [Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primeFactors,
      ne_eq, mul_ite, ite_mul, one_mul, mul_one]
    by_cases h : p.Prime; swap
    · simp only [h, false_and, if_false]
    simp only [h, true_and, if_true]
    by_cases hp' : p ∣ N; swap
    · simp only [hp', false_and, ↓reduceIte, inv_inj, sub_right_inj, mul_eq_mul_right_iff,
        cpow_eq_zero_iff, Nat.cast_eq_zero, h.ne_zero, ne_eq, neg_eq_zero, or_false]
      have hq : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd h).mpr hp'
      simp only [hq.unit_spec ▸ DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN hq.unit,
        ZMod.cast_natCast hMN]
    · simp only [hp', NeZero.ne N, not_false_eq_true, and_self, ↓reduceIte]
      have : ¬IsUnit (p : ZMod N) := by rwa [ZMod.isUnit_prime_iff_not_dvd h, not_not]
      rw [MulChar.map_nonunit _ this, zero_mul, sub_zero, inv_one]
      refine (inv_mul_cancel₀ ?_).symm
      rw [sub_ne_zero, ne_comm]
      apply_fun (‖·‖)
      simp only [norm_mul, norm_one]
      have ha : ‖χ p‖ ≤ 1 := χ.norm_le_one p
      have hb : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := norm_prime_cpow_le_one_half ⟨p, h⟩ hs
      exact ((mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_lt (by norm_num)).ne