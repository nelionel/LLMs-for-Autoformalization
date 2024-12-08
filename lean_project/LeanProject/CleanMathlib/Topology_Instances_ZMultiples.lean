import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Topology.Algebra.UniformGroup.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Metrizable.Basic
noncomputable section
open Filter Int Metric Set TopologicalSpace Bornology
open scoped Topology Uniformity Interval
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
namespace Int
open Metric
instance {a : ℝ} : DiscreteTopology (AddSubgroup.zmultiples a) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := (⊥ : Submodule ℤ ℝ))
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨ball 0 |a|, isOpen_ball, ?_⟩
  ext ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  simp [ha, Real.dist_eq, abs_mul, (by norm_cast : |(k : ℝ)| < 1 ↔ |k| < 1)]
theorem tendsto_coe_cofinite : Tendsto ((↑) : ℤ → ℝ) cofinite (cocompact ℝ) := by
  apply (castAddHom ℝ).tendsto_coe_cofinite_of_discrete cast_injective
  rw [range_castAddHom]
  infer_instance
theorem tendsto_zmultiplesHom_cofinite {a : ℝ} (ha : a ≠ 0) :
    Tendsto (zmultiplesHom ℝ a) cofinite (cocompact ℝ) := by
  apply (zmultiplesHom ℝ a).tendsto_coe_cofinite_of_discrete <| smul_left_injective ℤ ha
  rw [AddSubgroup.range_zmultiplesHom]
  infer_instance
end Int
namespace AddSubgroup
theorem tendsto_zmultiples_subtype_cofinite (a : ℝ) :
    Tendsto (zmultiples a).subtype cofinite (cocompact ℝ) :=
  (zmultiples a).tendsto_coe_cofinite_of_discrete
end AddSubgroup