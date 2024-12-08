import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Geometry.Manifold.ChartedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
def conformalPregroupoid : Pregroupoid X where
  property f u := ∀ x, x ∈ u → ConformalAt f x
  comp {f _} _ _ hf hg _ _ _ x hx := (hg (f x) hx.2).comp x (hf x hx.1)
  id_mem x _ := conformalAt_id x
  locality _ h x hx :=
    let ⟨_, _, h₂, h₃⟩ := h x hx
    h₃ x ⟨hx, h₂⟩
  congr hu h hf x hx := (hf x hx).congr hx hu h
def conformalGroupoid : StructureGroupoid X :=
  conformalPregroupoid.groupoid