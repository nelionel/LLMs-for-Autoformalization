import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt
open NormedSpace 
namespace DualNumber
open TrivSqZeroExt
variable (𝕜 : Type*) {R : Type*}
variable [Field 𝕜] [CharZero 𝕜] [CommRing R] [Algebra 𝕜 R]
variable [UniformSpace R] [TopologicalRing R] [T2Space R]
@[simp]
theorem exp_eps : exp 𝕜 (eps : DualNumber R) = 1 + eps :=
  exp_inr _ _
@[simp]
theorem exp_smul_eps (r : R) : exp 𝕜 (r • eps : DualNumber R) = 1 + r • eps := by
  rw [eps, ← inr_smul, exp_inr]
end DualNumber