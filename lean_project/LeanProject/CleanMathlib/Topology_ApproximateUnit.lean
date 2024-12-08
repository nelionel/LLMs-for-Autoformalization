import Mathlib.Topology.Algebra.Monoid
open Filter Topology
structure Filter.IsApproximateUnit {α : Type*} [TopologicalSpace α] [Mul α]
    (l : Filter α) : Prop where
  tendsto_mul_left m : Tendsto (m * ·) l (𝓝 m)
  tendsto_mul_right m : Tendsto (· * m) l (𝓝 m)
  protected [neBot : NeBot l]
namespace Filter.IsApproximateUnit
section TopologicalMonoid
variable {α : Type*} [TopologicalSpace α] [MulOneClass α]
variable (α) in
lemma pure_one : IsApproximateUnit (pure (1 : α))  where
  tendsto_mul_left m := by simpa using tendsto_pure_nhds (m * ·) (1 : α)
  tendsto_mul_right m := by simpa using tendsto_pure_nhds (· * m) (1 : α)
set_option linter.unusedVariables false in
lemma mono {l l' : Filter α} (hl : l.IsApproximateUnit) (hle : l' ≤ l) [hl' : l'.NeBot] :
    l'.IsApproximateUnit where
  tendsto_mul_left m := hl.tendsto_mul_left m |>.mono_left hle
  tendsto_mul_right m := hl.tendsto_mul_right m |>.mono_left hle
variable (α) in
lemma nhds_one [ContinuousMul α] : IsApproximateUnit (𝓝 (1 : α)) where
  tendsto_mul_left m := by simpa using tendsto_id (x := 𝓝 1) |>.const_mul m
  tendsto_mul_right m := by simpa using tendsto_id (x := 𝓝 1) |>.mul_const m
lemma iff_neBot_and_le_nhds_one [ContinuousMul α] {l : Filter α} :
    IsApproximateUnit l ↔ l.NeBot ∧ l ≤ 𝓝 1 :=
  ⟨fun hl ↦ ⟨hl.neBot, by simpa using hl.tendsto_mul_left 1⟩,
    And.elim fun _ hl ↦ nhds_one α |>.mono hl⟩
lemma iff_le_nhds_one [ContinuousMul α] {l : Filter α} [l.NeBot] :
    IsApproximateUnit l ↔ l ≤ 𝓝 1 := by
  simpa [iff_neBot_and_le_nhds_one] using fun _ ↦ ‹_›
end TopologicalMonoid
end Filter.IsApproximateUnit