import Mathlib.Analysis.SpecialFunctions.Exp
open Filter Topology Real
namespace Polynomial
theorem tendsto_div_exp_atTop (p : ℝ[X]) : Tendsto (fun x ↦ p.eval x / exp x) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | h_monomial n c => simpa [exp_neg, div_eq_mul_inv, mul_assoc]
    using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  | h_add p q hp hq => simpa [add_div] using hp.add hq
end Polynomial