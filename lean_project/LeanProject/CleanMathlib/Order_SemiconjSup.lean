import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Function.Conjugate
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.OrdContinuous
import Mathlib.Order.RelIso.Group
assert_not_exists Finset
variable {α β γ : Type*}
open Set
def IsOrderRightAdjoint [Preorder α] [Preorder β] (f : α → β) (g : β → α) :=
  ∀ y, IsLUB { x | f x ≤ y } (g y)
theorem isOrderRightAdjoint_sSup [CompleteLattice α] [Preorder β] (f : α → β) :
    IsOrderRightAdjoint f fun y => sSup { x | f x ≤ y } := fun _ => isLUB_sSup _
theorem isOrderRightAdjoint_csSup [ConditionallyCompleteLattice α] [Preorder β] (f : α → β)
    (hne : ∀ y, ∃ x, f x ≤ y) (hbdd : ∀ y, BddAbove { x | f x ≤ y }) :
    IsOrderRightAdjoint f fun y => sSup { x | f x ≤ y } := fun y => isLUB_csSup (hne y) (hbdd y)
namespace IsOrderRightAdjoint
protected theorem unique [PartialOrder α] [Preorder β] {f : α → β} {g₁ g₂ : β → α}
    (h₁ : IsOrderRightAdjoint f g₁) (h₂ : IsOrderRightAdjoint f g₂) : g₁ = g₂ :=
  funext fun y => (h₁ y).unique (h₂ y)
theorem right_mono [Preorder α] [Preorder β] {f : α → β} {g : β → α} (h : IsOrderRightAdjoint f g) :
    Monotone g := fun y₁ y₂ hy => ((h y₁).mono (h y₂)) fun _ hx => le_trans hx hy
theorem orderIso_comp [Preorder α] [Preorder β] [Preorder γ] {f : α → β} {g : β → α}
    (h : IsOrderRightAdjoint f g) (e : β ≃o γ) : IsOrderRightAdjoint (e ∘ f) (g ∘ e.symm) :=
  fun y => by simpa [e.le_symm_apply] using h (e.symm y)
theorem comp_orderIso [Preorder α] [Preorder β] [Preorder γ] {f : α → β} {g : β → α}
    (h : IsOrderRightAdjoint f g) (e : γ ≃o α) : IsOrderRightAdjoint (f ∘ e) (e.symm ∘ g) := by
  intro y
  change IsLUB (e ⁻¹' { x | f x ≤ y }) (e.symm (g y))
  rw [e.isLUB_preimage, e.apply_symm_apply]
  exact h y
end IsOrderRightAdjoint
namespace Function
theorem Semiconj.symm_adjoint [PartialOrder α] [Preorder β] {fa : α ≃o α} {fb : β ↪o β} {g : α → β}
    (h : Function.Semiconj g fa fb) {g' : β → α} (hg' : IsOrderRightAdjoint g g') :
    Function.Semiconj g' fb fa := by
  refine fun y => (hg' _).unique ?_
  rw [← fa.surjective.image_preimage { x | g x ≤ fb y }, preimage_setOf_eq]
  simp only [h.eq, fb.le_iff_le, fa.leftOrdContinuous (hg' _)]
variable {G : Type*}
theorem semiconj_of_isLUB [PartialOrder α] [Group G] (f₁ f₂ : G →* α ≃o α) {h : α → α}
    (H : ∀ x, IsLUB (range fun g' => (f₁ g')⁻¹ (f₂ g' x)) (h x)) (g : G) :
    Function.Semiconj h (f₂ g) (f₁ g) := by
  refine fun y => (H _).unique ?_
  have := (f₁ g).leftOrdContinuous (H y)
  rw [← range_comp, ← (Equiv.mulRight g).surjective.range_comp _] at this
  simpa [comp_def] using this
theorem sSup_div_semiconj [CompleteLattice α] [Group G] (f₁ f₂ : G →* α ≃o α) (g : G) :
    Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
  semiconj_of_isLUB f₁ f₂ (fun _ => isLUB_iSup) _
theorem csSup_div_semiconj [ConditionallyCompleteLattice α] [Group G] (f₁ f₂ : G →* α ≃o α)
    (hbdd : ∀ x, BddAbove (range fun g => (f₁ g)⁻¹ (f₂ g x))) (g : G) :
    Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
  semiconj_of_isLUB f₁ f₂ (fun x => isLUB_csSup (range_nonempty _) (hbdd x)) _
end Function