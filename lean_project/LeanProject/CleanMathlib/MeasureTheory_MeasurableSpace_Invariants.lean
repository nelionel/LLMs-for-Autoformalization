import Mathlib.MeasureTheory.MeasurableSpace.Defs
open Set Function
open scoped MeasureTheory
namespace MeasurableSpace
variable {α : Type*}
def invariants [m : MeasurableSpace α] (f : α → α) : MeasurableSpace α :=
  { m ⊓ ⟨fun s ↦ f ⁻¹' s = s, by simp, by simp, fun f hf ↦ by simp [hf]⟩ with
    MeasurableSet' := fun s ↦ MeasurableSet[m] s ∧ f ⁻¹' s = s }
variable [MeasurableSpace α]
theorem measurableSet_invariants {f : α → α} {s : Set α} :
    MeasurableSet[invariants f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s :=
  .rfl
@[simp]
theorem invariants_id : invariants (id : α → α) = ‹MeasurableSpace α› :=
  ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, rfl⟩⟩
theorem invariants_le (f : α → α) : invariants f ≤ ‹MeasurableSpace α› := fun _ ↦ And.left
theorem inf_le_invariants_comp (f g : α → α) :
    invariants f ⊓ invariants g ≤ invariants (f ∘ g) := fun s hs ↦
  ⟨hs.1.1, by rw [preimage_comp, hs.1.2, hs.2.2]⟩
theorem le_invariants_iterate (f : α → α) (n : ℕ) :
    invariants f ≤ invariants (f^[n]) := by
  induction n with
  | zero => simp [invariants_le]
  | succ n ihn => exact le_trans (le_inf ihn le_rfl) (inf_le_invariants_comp _ _)
variable {β : Type*} [MeasurableSpace β]
theorem measurable_invariants_dom {f : α → α} {g : α → β} :
    Measurable[invariants f] g ↔ Measurable g ∧ ∀ s, MeasurableSet s → (g ∘ f) ⁻¹' s = g ⁻¹' s := by
  simp only [Measurable, ← forall_and]; rfl
theorem measurable_invariants_of_semiconj {fa : α → α} {fb : β → β} {g : α → β} (hg : Measurable g)
    (hfg : Semiconj g fa fb) : @Measurable _ _ (invariants fa) (invariants fb) g := fun s hs ↦
  ⟨hg hs.1, by rw [← preimage_comp, hfg.comp_eq, preimage_comp, hs.2]⟩
end MeasurableSpace