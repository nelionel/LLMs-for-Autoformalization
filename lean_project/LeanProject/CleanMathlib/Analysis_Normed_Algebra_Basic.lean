import Mathlib.Topology.Algebra.Module.CharacterSpace
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Algebra.Spectrum
variable {𝕜 : Type*} {A : Type*}
namespace WeakDual
namespace CharacterSpace
variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
theorem norm_le_norm_one (φ : characterSpace 𝕜 A) : ‖toNormedDual (φ : WeakDual 𝕜 A)‖ ≤ ‖(1 : A)‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (1 : A)) fun a =>
    mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ a)
instance [ProperSpace 𝕜] : CompactSpace (characterSpace 𝕜 A) := by
  rw [← isCompact_iff_compactSpace]
  have h : characterSpace 𝕜 A ⊆ toNormedDual ⁻¹' Metric.closedBall 0 ‖(1 : A)‖ := by
    intro φ hφ
    rw [Set.mem_preimage, mem_closedBall_zero_iff]
    exact (norm_le_norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ : _)
  exact (isCompact_closedBall 𝕜 0 _).of_isClosed_subset CharacterSpace.isClosed h
end CharacterSpace
end WeakDual