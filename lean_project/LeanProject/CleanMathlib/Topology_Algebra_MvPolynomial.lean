import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Ring.Basic
variable {X σ : Type*} [TopologicalSpace X] [CommSemiring X] [TopologicalSemiring X]
  (p : MvPolynomial σ X)
theorem MvPolynomial.continuous_eval : Continuous fun x ↦ eval x p := by
  continuity