import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
noncomputable section
open scoped BoundedContinuousFunction unitInterval
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I
@[simp]
theorem bernstein_apply (n ν : ℕ) (x : I) :
    bernstein n ν x = (n.choose ν : ℝ) * (x : ℝ) ^ ν * (1 - (x : ℝ)) ^ (n - ν) := by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp
theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x := by
  simp only [bernstein_apply]
  have h₁ : (0 : ℝ) ≤ x := by unit_interval
  have h₂ : (0 : ℝ) ≤ 1 - x := by unit_interval
  positivity
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function
@[positivity DFunLike.coe _ _]
def evalBernstein : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _coe (.app (.app _ n) ν)) x ← whnfR e | throwError "not bernstein polynomial"
  let p ← mkAppOptM ``bernstein_nonneg #[n, ν, x]
  pure (.nonnegative p)
end Mathlib.Meta.Positivity
namespace bernstein
def z {n : ℕ} (k : Fin (n + 1)) : I :=
  ⟨(k : ℝ) / n, by
    cases' n with n
    · norm_num
    · have h₁ : 0 < (n.succ : ℝ) := mod_cast Nat.succ_pos _
      have h₂ : ↑k ≤ n.succ := mod_cast Fin.le_last k
      rw [Set.mem_Icc, le_div_iff₀ h₁, div_le_iff₀ h₁]
      norm_cast
      simp [h₂]⟩
local postfix:90 "/ₙ" => z
theorem probability (n : ℕ) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1 := by
  have := bernsteinPolynomial.sum ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  simp? [map_sum, Finset.sum_range] at this says
    simp only [Finset.sum_range, map_sum, Polynomial.coe_aeval_eq_eval, Polynomial.eval_one] at this
  exact this
theorem variance {n : ℕ} (h : 0 < (n : ℝ)) (x : I) :
    (∑ k : Fin (n + 1), (x - k/ₙ : ℝ) ^ 2 * bernstein n k x) = (x : ℝ) * (1 - x) / n := by
  have h' : (n : ℝ) ≠ 0 := ne_of_gt h
  apply_fun fun x : ℝ => x * n using GroupWithZero.mul_left_injective h'
  apply_fun fun x : ℝ => x * n using GroupWithZero.mul_left_injective h'
  dsimp
  conv_lhs => simp only [Finset.sum_mul, z]
  conv_rhs => rw [div_mul_cancel₀ _ h']
  have := bernsteinPolynomial.variance ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  simp? [map_sum, Finset.sum_range, ← Polynomial.natCast_mul] at this says
    simp only [nsmul_eq_mul, Finset.sum_range, map_sum, Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_natCast,
      Polynomial.eval_X, Polynomial.eval_one] at this
  convert this using 1
  · congr 1; funext k
    rw [mul_comm _ (n : ℝ), mul_comm _ (n : ℝ), ← mul_assoc, ← mul_assoc]
    congr 1
    field_simp [h]
    ring
  · ring
end bernstein
open bernstein
local postfix:1024 "/ₙ" => z
def bernsteinApproximation (n : ℕ) (f : C(I, ℝ)) : C(I, ℝ) :=
  ∑ k : Fin (n + 1), f k/ₙ • bernstein n k
namespace bernsteinApproximation
@[simp]
theorem apply (n : ℕ) (f : C(I, ℝ)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Fin (n + 1), f k/ₙ * bernstein n k x := by
  simp [bernsteinApproximation]
def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)
theorem δ_pos {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} : 0 < δ f ε h :=
  f.modulus_pos
def S (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : Finset (Fin (n + 1)) :=
  {k : Fin (n + 1) | dist k/ₙ x < δ f ε h}.toFinset
theorem lt_of_mem_S {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ S f ε h n x) : |f k/ₙ - f x| < ε / 2 := by
  apply f.dist_lt_of_dist_lt_modulus (ε / 2) (half_pos h)
  simpa [S, (Set.mem_toFinset)] using m
theorem le_of_mem_S_compl {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ (S f ε h n x)ᶜ) : (1 : ℝ) ≤ δ f ε h ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 := by
  simp only [Finset.mem_compl, not_lt, Set.mem_toFinset, Set.mem_setOf_eq, S] at m
  rw [zpow_neg, ← div_eq_inv_mul, zpow_two, ← pow_two, one_le_div (pow_pos δ_pos 2), sq_le_sq,
    abs_of_pos δ_pos]
  rwa [dist_comm] at m
end bernsteinApproximation
open bernsteinApproximation
open BoundedContinuousFunction
open Filter
open scoped Topology
theorem bernsteinApproximation_uniform (f : C(I, ℝ)) :
    Tendsto (fun n : ℕ => bernsteinApproximation n f) atTop (𝓝 f) := by
  simp only [Metric.nhds_basis_ball.tendsto_right_iff, Metric.mem_ball, dist_eq_norm]
  intro ε h
  let δ := δ f ε h
  have nhds_zero := tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖ * δ ^ (-2 : ℤ))
  filter_upwards [nhds_zero.eventually (gt_mem_nhds (half_pos h)), eventually_gt_atTop 0] with n nh
    npos'
  have npos : 0 < (n : ℝ) := by positivity
  rw [ContinuousMap.norm_lt_iff _ h]
  intro x
  let S := S f ε h n x
  calc
    |(bernsteinApproximation n f - f) x| = |bernsteinApproximation n f x - f x| := rfl
    _ = |bernsteinApproximation n f x - f x * 1| := by rw [mul_one]
    _ = |bernsteinApproximation n f x - f x * ∑ k : Fin (n + 1), bernstein n k x| := by
      rw [bernstein.probability]
    _ = |∑ k : Fin (n + 1), (f k/ₙ - f x) * bernstein n k x| := by
      simp [bernsteinApproximation, Finset.mul_sum, sub_mul]
    _ ≤ ∑ k : Fin (n + 1), |(f k/ₙ - f x) * bernstein n k x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (n + 1), |f k/ₙ - f x| * bernstein n k x := by
      simp_rw [abs_mul, abs_eq_self.mpr bernstein_nonneg]
    _ = (∑ k ∈ S, |f k/ₙ - f x| * bernstein n k x) + ∑ k ∈ Sᶜ, |f k/ₙ - f x| * bernstein n k x :=
      (S.sum_add_sum_compl _).symm
    _ < ε / 2 + ε / 2 :=
      (add_lt_add_of_le_of_lt ?_ ?_)
    _ = ε := add_halves ε
  · 
    calc
      ∑ k ∈ S, |f k/ₙ - f x| * bernstein n k x ≤ ∑ k ∈ S, ε / 2 * bernstein n k x := by
        gcongr with _ m
        exact le_of_lt (lt_of_mem_S m)
      _ = ε / 2 * ∑ k ∈ S, bernstein n k x := by rw [Finset.mul_sum]
      _ ≤ ε / 2 * ∑ k : Fin (n + 1), bernstein n k x := by gcongr; exact S.subset_univ
      _ = ε / 2 := by rw [bernstein.probability, mul_one]
  · 
    calc
      ∑ k ∈ Sᶜ, |f k/ₙ - f x| * bernstein n k x ≤ ∑ k ∈ Sᶜ, 2 * ‖f‖ * bernstein n k x := by
        gcongr
        apply f.dist_le_two_norm
      _ = 2 * ‖f‖ * ∑ k ∈ Sᶜ, bernstein n k x := by rw [Finset.mul_sum]
      _ ≤ 2 * ‖f‖ * ∑ k ∈ Sᶜ, δ ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        gcongr with _ m
        conv_lhs => rw [← one_mul (bernstein _ _ _)]
        gcongr
        exact le_of_mem_S_compl m
      _ ≤ 2 * ‖f‖ * ∑ k : Fin (n + 1), δ ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        gcongr; exact Sᶜ.subset_univ
      _ = 2 * ‖f‖ * δ ^ (-2 : ℤ) * ∑ k : Fin (n + 1), ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        conv_rhs =>
          rw [mul_assoc, Finset.mul_sum]
          simp only [← mul_assoc]
      _ = 2 * ‖f‖ * δ ^ (-2 : ℤ) * x * (1 - x) / n := by rw [variance npos]; ring
      _ ≤ 2 * ‖f‖ * δ ^ (-2 : ℤ) * 1 * 1 / n := by gcongr <;> unit_interval
      _ < ε / 2 := by simp only [mul_one]; exact nh