import Mathlib.MeasureTheory.Measure.MeasureSpace
namespace MeasureTheory
class VAddInvariantMeasure (M α : Type*) [VAdd M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_vadd : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s
@[to_additive, mk_iff smulInvariantMeasure_iff]
class SMulInvariantMeasure (M α : Type*) [SMul M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_smul : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c • x) ⁻¹' s) = μ s
attribute [to_additive] smulInvariantMeasure_iff
namespace Measure
variable {G : Type*} [MeasurableSpace G]
class IsAddLeftInvariant [Add G] (μ : Measure G) : Prop where
  map_add_left_eq_self : ∀ g : G, map (g + ·) μ = μ
@[to_additive existing]
class IsMulLeftInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_left_eq_self : ∀ g : G, map (g * ·) μ = μ
class IsAddRightInvariant [Add G] (μ : Measure G) : Prop where
  map_add_right_eq_self : ∀ g : G, map (· + g) μ = μ
@[to_additive existing]
class IsMulRightInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_right_eq_self : ∀ g : G, map (· * g) μ = μ
variable {μ : Measure G}
@[to_additive]
instance IsMulLeftInvariant.smulInvariantMeasure  [Mul G] [IsMulLeftInvariant μ] :
    SMulInvariantMeasure G G μ :=
  ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_left_eq_self _) hs.nullMeasurableSet⟩
@[to_additive]
instance [Monoid G] (s : Submonoid G) [IsMulLeftInvariant μ] :
    SMulInvariantMeasure {x // x ∈ s} G μ :=
  ⟨fun ⟨x, _⟩ _ h ↦ IsMulLeftInvariant.smulInvariantMeasure.1 x h⟩
@[to_additive]
instance IsMulRightInvariant.toSMulInvariantMeasure_op  [Mul G] [μ.IsMulRightInvariant] :
    SMulInvariantMeasure Gᵐᵒᵖ G μ :=
  ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_right_eq_self _) hs.nullMeasurableSet⟩
end Measure
end MeasureTheory