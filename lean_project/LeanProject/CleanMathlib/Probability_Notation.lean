import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Decomposition.Lebesgue
open MeasureTheory
open scoped MeasureTheory
scoped[ProbabilityTheory] notation "𝔼[" X "|" m "]" =>
  MeasureTheory.condexp m MeasureTheory.MeasureSpace.volume X
set_option quotPrecheck false in
scoped[ProbabilityTheory] notation P "[" X "]" => ∫ x, ↑(X x) ∂P
scoped[ProbabilityTheory] notation "𝔼[" X "]" => ∫ a, (X : _ → _) a
scoped[ProbabilityTheory] notation P "⟦" s "|" m "⟧" =>
  MeasureTheory.condexp m P (Set.indicator s fun ω => (1 : ℝ))
scoped[ProbabilityTheory] notation:50 X " =ₐₛ " Y:50 => X =ᵐ[MeasureTheory.MeasureSpace.volume] Y
scoped[ProbabilityTheory] notation:50 X " ≤ₐₛ " Y:50 => X ≤ᵐ[MeasureTheory.MeasureSpace.volume] Y
scoped[ProbabilityTheory] notation "∂" P "/∂" Q:100 => MeasureTheory.Measure.rnDeriv P Q
scoped[ProbabilityTheory] notation "ℙ" => MeasureTheory.MeasureSpace.volume