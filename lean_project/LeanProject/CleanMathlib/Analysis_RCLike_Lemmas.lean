import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
variable {K E : Type*} [RCLike K]
namespace Polynomial
theorem ofReal_eval (p : ℝ[X]) (x : ℝ) : (↑(p.eval x) : K) = aeval (↑x) p :=
  (@aeval_algebraMap_apply_eq_algebraMap_eval ℝ K _ _ _ x p).symm
end Polynomial
namespace FiniteDimensional
open scoped Classical
open RCLike
library_note "RCLike instance"
instance rclike_to_real : FiniteDimensional ℝ K :=
  ⟨{1, I}, by
    suffices ∀ x : K, ∃ a b : ℝ, a • 1 + b • I = x by
      simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
    exact fun x ↦ ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩⟩
variable (K E)
variable [NormedAddCommGroup E] [NormedSpace K E]
theorem proper_rclike [FiniteDimensional K E] : ProperSpace E := by
  letI : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ K E
  letI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance
variable {E}
instance RCLike.properSpace_submodule (S : Submodule K E) [FiniteDimensional K S] :
    ProperSpace S :=
  proper_rclike K S
end FiniteDimensional
namespace RCLike
@[simp, rclike_simps]
theorem reCLM_norm : ‖(reCLM : K →L[ℝ] ℝ)‖ = 1 := by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert ContinuousLinearMap.ratio_le_opNorm (reCLM : K →L[ℝ] ℝ) (1 : K)
  simp
@[simp, rclike_simps]
theorem conjCLE_norm : ‖(@conjCLE K _ : K →L[ℝ] K)‖ = 1 :=
  (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap
@[simp, rclike_simps]
theorem ofRealCLM_norm : ‖(ofRealCLM : ℝ →L[ℝ] K)‖ = 1 :=
  LinearIsometry.norm_toContinuousLinearMap _
end RCLike
namespace Polynomial
open ComplexConjugate in
lemma aeval_conj (p : ℝ[X]) (z : K) : aeval (conj z) p = conj (aeval z p) :=
  aeval_algHom_apply (RCLike.conjAe (K := K)) z p
lemma aeval_ofReal (p : ℝ[X]) (x : ℝ) : aeval (RCLike.ofReal x : K) p = eval x p :=
  aeval_algHom_apply RCLike.ofRealAm x p
end Polynomial