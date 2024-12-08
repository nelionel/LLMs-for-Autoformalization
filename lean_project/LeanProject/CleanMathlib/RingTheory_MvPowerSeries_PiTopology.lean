import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.UniformGroup.Basic
import Mathlib.Topology.UniformSpace.Pi
namespace MvPowerSeries
open Function Filter
variable {σ R : Type*}
namespace WithPiTopology
section Topology
variable [TopologicalSpace R]
variable (R) in
scoped instance : TopologicalSpace (MvPowerSeries σ R) :=
  Pi.topologicalSpace
@[scoped instance]
theorem instT0Space [T0Space R] : T0Space (MvPowerSeries σ R) := Pi.instT0Space
@[scoped instance]
theorem instT2Space [T2Space R] : T2Space (MvPowerSeries σ R) := Pi.t2Space
variable (R) in
@[fun_prop]
theorem continuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    Continuous (MvPowerSeries.coeff R d) :=
  continuous_pi_iff.mp continuous_id d
variable (R) in
theorem continuous_constantCoeff [Semiring R] : Continuous (constantCoeff σ R) :=
  continuous_coeff R 0
theorem tendsto_iff_coeff_tendsto [Semiring R] {ι : Type*}
    (f : ι → MvPowerSeries σ R) (u : Filter ι) (g : MvPowerSeries σ R) :
    Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Tendsto (fun i => coeff R d (f i)) u (nhds (coeff R d g)) := by
  rw [nhds_pi, tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)
variable (σ R)
@[scoped instance]
theorem instTopologicalSemiring [Semiring R] [TopologicalSemiring R] :
    TopologicalSemiring (MvPowerSeries σ R) where
    continuous_add := continuous_pi fun d => continuous_add.comp
      (((continuous_coeff R d).fst').prod_mk (continuous_coeff R d).snd')
    continuous_mul := continuous_pi fun _ =>
      continuous_finset_sum _ fun i _ => continuous_mul.comp
        ((continuous_coeff R i.fst).fst'.prod_mk (continuous_coeff R i.snd).snd')
@[scoped instance]
theorem instTopologicalRing [Ring R] [TopologicalRing R] :
    TopologicalRing (MvPowerSeries σ R) :=
  { instTopologicalSemiring σ R with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg
      (continuous_coeff R d) }
variable {σ R}
@[fun_prop]
theorem continuous_C [Semiring R] :
    Continuous (C σ R) := by
  classical
  simp only [continuous_iff_continuousAt]
  refine fun r ↦ (tendsto_iff_coeff_tendsto _ _ _).mpr fun d ↦ ?_
  simp only [coeff_C]
  split_ifs
  · exact tendsto_id
  · exact tendsto_const_nhds
theorem variables_tendsto_zero [Semiring R] :
    Tendsto (X · : σ → MvPowerSeries σ R) cofinite (nhds 0) := by
  classical
  simp only [tendsto_iff_coeff_tendsto, ← coeff_apply, coeff_X, coeff_zero]
  refine fun d ↦ tendsto_nhds_of_eventually_eq ?_
  by_cases h : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, hi⟩ := h
    filter_upwards [eventually_cofinite_ne i] with j hj
    simp [hi, Finsupp.single_eq_single_iff, hj.symm]
  · simpa only [ite_eq_right_iff] using
      Eventually.of_forall fun x h' ↦ (not_exists.mp h x h').elim
theorem tendsto_pow_zero_of_constantCoeff_nilpotent [CommSemiring R]
    {f} (hf : IsNilpotent (constantCoeff σ R f)) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d ↦ tendsto_atTop_of_eventually_const fun n hn ↦
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn
theorem tendsto_pow_zero_of_constantCoeff_zero [CommSemiring R]
    {f} (hf : constantCoeff σ R f = 0) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) := by
  apply tendsto_pow_zero_of_constantCoeff_nilpotent
  rw [hf]
  exact IsNilpotent.zero
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [CommRing R] [DiscreteTopology R] (f) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) ↔
      IsNilpotent (constantCoeff σ R f) := by
  refine ⟨?_, tendsto_pow_zero_of_constantCoeff_nilpotent⟩
  intro h
  suffices Tendsto (fun n : ℕ => constantCoeff σ R (f ^ n)) atTop (nhds 0) by
    simp only [tendsto_def] at this
    specialize this {0} _
    suffices ∀ x : R, {x} ∈ nhds x by exact this 0
    rw [← discreteTopology_iff_singleton_mem_nhds]; infer_instance
    simp only [map_pow, mem_atTop_sets, ge_iff_le, Set.mem_preimage,
      Set.mem_singleton_iff] at this
    obtain ⟨m, hm⟩ := this
    use m
    apply hm m (le_refl m)
  simp only [← @comp_apply _ R ℕ, ← tendsto_map'_iff]
  simp only [Tendsto, map_le_iff_le_comap] at h ⊢
  refine le_trans h (comap_mono ?_)
  rw [← map_le_iff_le_comap]
  exact Continuous.continuousAt (continuous_constantCoeff R)
variable [Semiring R]
theorem hasSum_of_monomials_self (f : MvPowerSeries σ R) :
    HasSum (fun d : σ →₀ ℕ => monomial R d (coeff R d f)) f := by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single d ?_ using 1
  · exact (coeff_monomial_same d _).symm
  · exact fun d' h ↦ coeff_monomial_ne (Ne.symm h) _
theorem as_tsum [T2Space R] (f : MvPowerSeries σ R) :
    f = tsum fun d : σ →₀ ℕ => monomial R d (coeff R d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm
end Topology
section Uniformity
variable [UniformSpace R]
scoped instance : UniformSpace (MvPowerSeries σ R) :=
  Pi.uniformSpace fun _ : σ →₀ ℕ => R
variable (R) in
theorem uniformContinuous_coeff [Semiring R] (d : σ →₀ ℕ) :
    UniformContinuous fun f : MvPowerSeries σ R => coeff R d f :=
  uniformContinuous_pi.mp uniformContinuous_id d
@[scoped instance]
theorem instCompleteSpace [CompleteSpace R] :
    CompleteSpace (MvPowerSeries σ R) := Pi.complete _
@[scoped instance]
theorem instUniformAddGroup [AddGroup R] [UniformAddGroup R] :
    UniformAddGroup (MvPowerSeries σ R) := Pi.instUniformAddGroup
end Uniformity
end WithPiTopology
end MvPowerSeries