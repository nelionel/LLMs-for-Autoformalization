import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Card
instance Mathlib.Vector.finite {α : Type*} [Finite α] {n : ℕ} : Finite (Vector α n) := by
  haveI := Fintype.ofFinite α
  infer_instance