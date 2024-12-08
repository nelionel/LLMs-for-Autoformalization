import Mathlib.Data.Fintype.Lattice
import Mathlib.RingTheory.Finiteness.Basic
namespace Submodule
open Module
variable {R V} [Ring R] [AddCommGroup V] [Module R V]
instance finite_iSup {ι : Sort*} [Finite ι] (S : ι → Submodule R V)
    [∀ i, Module.Finite R (S i)] : Module.Finite R ↑(⨆ i, S i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup_univ_eq_iSup]
  exact Submodule.finite_finset_sup _ _
end Submodule