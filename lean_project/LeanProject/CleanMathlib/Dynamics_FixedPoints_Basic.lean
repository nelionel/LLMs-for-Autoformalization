import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Iterate
import Mathlib.GroupTheory.Perm.Basic
open Equiv
universe u v
variable {α : Type u} {β : Type v} {f fa g : α → α} {x : α} {fb : β → β} {e : Perm α}
namespace Function
open Function (Commute)
theorem isFixedPt_id (x : α) : IsFixedPt id x :=
  (rfl : _)
namespace IsFixedPt
instance decidable [h : DecidableEq α] {f : α → α} {x : α} : Decidable (IsFixedPt f x) :=
  h (f x) x
protected theorem eq (hf : IsFixedPt f x) : f x = x :=
  hf
protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
  calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf
protected theorem iterate (hf : IsFixedPt f x) (n : ℕ) : IsFixedPt f^[n] x :=
  iterate_fixed hf n
theorem left_of_comp (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x) : IsFixedPt f x :=
  calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg
theorem to_leftInverse (hf : IsFixedPt f x) (h : LeftInverse g f) : IsFixedPt g x :=
  calc
    g x = g (f x) := congr_arg g hf.symm
    _ = x := h x
protected theorem map {x : α} (hx : IsFixedPt fa x) {g : α → β} (h : Semiconj g fa fb) :
    IsFixedPt fb (g x) :=
  calc
    fb (g x) = g (fa x) := (h.eq x).symm
    _ = g x := congr_arg g hx
protected theorem apply {x : α} (hx : IsFixedPt f x) : IsFixedPt f (f x) := by convert hx
theorem preimage_iterate {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : ℕ) :
    IsFixedPt (Set.preimage f^[n]) s := by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n
lemma image_iterate {s : Set α} (h : IsFixedPt (Set.image f) s) (n : ℕ) :
    IsFixedPt (Set.image f^[n]) s :=
  Set.image_iterate_eq ▸ h.iterate n
protected theorem equiv_symm (h : IsFixedPt e x) : IsFixedPt e.symm x :=
  h.to_leftInverse e.leftInverse_symm
protected theorem perm_inv (h : IsFixedPt e x) : IsFixedPt (⇑e⁻¹) x :=
  h.equiv_symm
protected theorem perm_pow (h : IsFixedPt e x) (n : ℕ) : IsFixedPt (⇑(e ^ n)) x := h.iterate _
protected theorem perm_zpow (h : IsFixedPt e x) : ∀ n : ℤ, IsFixedPt (⇑(e ^ n)) x
  | Int.ofNat _ => h.perm_pow _
  | Int.negSucc n => (h.perm_pow <| n + 1).perm_inv
end IsFixedPt
@[simp]
theorem Injective.isFixedPt_apply_iff (hf : Injective f) {x : α} :
    IsFixedPt f (f x) ↔ IsFixedPt f x :=
  ⟨fun h => hf h.eq, IsFixedPt.apply⟩
def fixedPoints (f : α → α) : Set α :=
  { x : α | IsFixedPt f x }
instance fixedPoints.decidable [DecidableEq α] (f : α → α) (x : α) :
    Decidable (x ∈ fixedPoints f) :=
  IsFixedPt.decidable
@[simp]
theorem mem_fixedPoints : x ∈ fixedPoints f ↔ IsFixedPt f x :=
  Iff.rfl
theorem mem_fixedPoints_iff {α : Type*} {f : α → α} {x : α} : x ∈ fixedPoints f ↔ f x = x := by
  rfl
@[simp]
theorem fixedPoints_id : fixedPoints (@id α) = Set.univ :=
  Set.ext fun _ => by simpa using isFixedPt_id _
theorem fixedPoints_subset_range : fixedPoints f ⊆ Set.range f := fun x hx => ⟨x, hx⟩
theorem Semiconj.mapsTo_fixedPoints {g : α → β} (h : Semiconj g fa fb) :
    Set.MapsTo g (fixedPoints fa) (fixedPoints fb) := fun _ hx => hx.map h
theorem invOn_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  ⟨fun _ => id, fun _ => id⟩
theorem mapsTo_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.MapsTo f (fixedPoints <| g ∘ f) (fixedPoints <| f ∘ g) := fun _ hx => hx.map fun _ => rfl
theorem bijOn_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  (invOn_fixedPoints_comp f g).bijOn (mapsTo_fixedPoints_comp g f) (mapsTo_fixedPoints_comp f g)
theorem Commute.invOn_fixedPoints_comp (h : Commute f g) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using Function.invOn_fixedPoints_comp f g
theorem Commute.left_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn f (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp g f
theorem Commute.right_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp f g
end Function