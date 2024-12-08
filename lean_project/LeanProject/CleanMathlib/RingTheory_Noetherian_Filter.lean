import Mathlib.Order.Filter.EventuallyConst
import Mathlib.RingTheory.Noetherian.Defs
open Set Filter Pointwise
open IsNoetherian Submodule Function
section Semiring
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
theorem eventuallyConst_of_isNoetherian [IsNoetherian R M] (f : ℕ →o Submodule R M) :
    atTop.EventuallyConst f := by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact (monotone_stabilizes_iff_noetherian.mpr inferInstance) f
end Semiring