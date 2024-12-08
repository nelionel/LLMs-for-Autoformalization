import Mathlib.RingTheory.SimpleModule
import Mathlib.Topology.Algebra.Module.Basic
universe u v w
variable {R : Type u} {M : Type v} {N : Type w} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [ContinuousSMul R M] [Module R N] [ContinuousAdd M]
  [IsSimpleModule R N]
theorem LinearMap.isClosed_or_dense_ker (l : M →ₗ[R] N) :
    IsClosed (LinearMap.ker l : Set M) ∨ Dense (LinearMap.ker l : Set M) := by
  rcases l.surjective_or_eq_zero with (hl | rfl)
  · exact l.ker.isClosed_or_dense_of_isCoatom (LinearMap.isCoatom_ker_of_surjective hl)
  · rw [LinearMap.ker_zero]
    left
    exact isClosed_univ