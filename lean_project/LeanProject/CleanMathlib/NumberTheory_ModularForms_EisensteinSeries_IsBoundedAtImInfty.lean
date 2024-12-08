import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.NumberTheory.ModularForms.Identities
noncomputable section
open ModularForm UpperHalfPlane  Matrix SlashInvariantForm CongruenceSubgroup
open scoped MatrixGroups
namespace EisensteinSeries
lemma summable_norm_eisSummand {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖ := by
  have hk' : (2 : ℝ) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : ℝ)).of_nonneg_of_le
    (fun _ => Complex.abs.nonneg _)
  intro b
  simp only [eisSummand, map_zpow₀]
  exact_mod_cast summand_bound z (show 0 ≤ (k : ℝ) by positivity) b
lemma abs_le_tsum_abs (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    Complex.abs (eisensteinSeries a k z) ≤ ∑' (x : Fin 2 → ℤ), Complex.abs (eisSummand k x z) := by
  simp_rw [← Complex.norm_eq_abs, eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (tsum_subtype_le (fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖) _ (fun _ ↦ norm_nonneg _)
      (summable_norm_eisSummand hk z))
theorem isBoundedAtImInfty_eisensteinSeries_SIF {N : ℕ+} (a : Fin 2 → ZMod N) {k : ℤ} (hk : 3 ≤ k)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[k] A) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, eisensteinSeries_SIF] at *
  refine ⟨∑'(x : Fin 2 → ℤ), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z N.2)
  rw [eisensteinSeries_slash_apply, ← eisensteinSeries_SIF_apply,
    ← T_zpow_width_invariant N k n (eisensteinSeries_SIF (a ᵥ* A) k) z]
  apply le_trans (abs_le_tsum_abs N (a ᵥ* A) k hk _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply tsum_le_tsum _ (summable_norm_eisSummand hk _)
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)
end EisensteinSeries