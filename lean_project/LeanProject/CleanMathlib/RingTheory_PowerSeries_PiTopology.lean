import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
namespace PowerSeries
open Filter Function
variable (R : Type*)
section Topological
variable [TopologicalSpace R]
namespace WithPiTopology
scoped instance : TopologicalSpace (PowerSeries R) :=
  Pi.topologicalSpace
@[scoped instance]
theorem instT0Space [T0Space R] : T0Space (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instT0Space
@[scoped instance]
theorem instT2Space [T2Space R] : T2Space (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instT2Space
theorem continuous_coeff [Semiring R] (d : ℕ) : Continuous (PowerSeries.coeff R d) :=
  continuous_pi_iff.mp continuous_id (Finsupp.single () d)
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff R) :=
  coeff_zero_eq_constantCoeff (R := R) ▸ continuous_coeff R 0
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → PowerSeries R) (u : Filter ι) (g : PowerSeries R) :
    Tendsto f u (nhds g) ↔
    ∀ d : ℕ, Tendsto (fun i => coeff R d (f i)) u (nhds (coeff R d g)) := by
  rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  apply (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.forall_congr
  intro d
  simp only [LinearEquiv.coe_toEquiv, Finsupp.LinearEquiv.finsuppUnique_apply,
    PUnit.default_eq_unit, coeff]
  apply iff_of_eq
  congr
  · ext _; congr; ext; simp
  · ext; simp
@[scoped instance]
theorem instTopologicalSemiring [Semiring R] [TopologicalSemiring R] :
    TopologicalSemiring (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instTopologicalSemiring Unit R
@[scoped instance]
theorem instTopologicalRing [Ring R] [TopologicalRing R] :
    TopologicalRing (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instTopologicalRing Unit R
end WithPiTopology
end Topological
section Uniform
namespace WithPiTopology
variable [UniformSpace R]
scoped instance : UniformSpace (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instUniformSpace
theorem uniformContinuous_coeff [Semiring R] (d : ℕ) :
    UniformContinuous fun f : PowerSeries R ↦ coeff R d f :=
  uniformContinuous_pi.mp uniformContinuous_id (Finsupp.single () d)
@[scoped instance]
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instCompleteSpace
@[scoped instance]
theorem instUniformAddGroup [AddGroup R] [UniformAddGroup R] :
    UniformAddGroup (PowerSeries R) :=
  MvPowerSeries.WithPiTopology.instUniformAddGroup
end WithPiTopology
end Uniform
section
variable {R}
variable [TopologicalSpace R]
namespace WithPiTopology
open MvPowerSeries.WithPiTopology
theorem continuous_C [Semiring R] : Continuous (C R) :=
  MvPowerSeries.WithPiTopology.continuous_C
theorem tendsto_pow_zero_of_constantCoeff_nilpotent [CommSemiring R]
    {f : PowerSeries R} (hf : IsNilpotent (constantCoeff R f)) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.tendsto_pow_zero_of_constantCoeff_nilpotent hf
theorem tendsto_pow_zero_of_constantCoeff_zero [CommSemiring R]
    {f : PowerSeries R} (hf : constantCoeff R f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) :=
  MvPowerSeries.WithPiTopology.tendsto_pow_zero_of_constantCoeff_zero hf
theorem tendsto_pow_zero_of_constantCoeff_nilpotent_iff
    [CommRing R] [DiscreteTopology R] (f : PowerSeries R) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) ↔
      IsNilpotent (constantCoeff R f) :=
  MvPowerSeries.WithPiTopology.tendsto_pow_of_constantCoeff_nilpotent_iff f
end WithPiTopology
end
section Summable
variable [Semiring R] [TopologicalSpace R]
open WithPiTopology MvPowerSeries.WithPiTopology
variable {R}
theorem hasSum_of_monomials_self (f : PowerSeries R) :
    HasSum (fun d : ℕ => monomial R d (coeff R d f)) f := by
  rw [← (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.hasSum_iff]
  convert MvPowerSeries.WithPiTopology.hasSum_of_monomials_self f
  simp only [LinearEquiv.coe_toEquiv, comp_apply, monomial, coeff,
    Finsupp.LinearEquiv.finsuppUnique_apply, PUnit.default_eq_unit]
  congr
  all_goals { ext; simp }
theorem as_tsum [T2Space R] (f : PowerSeries R) :
    f = tsum fun d : ℕ => monomial R d (coeff R d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self f)).symm
end Summable
end PowerSeries