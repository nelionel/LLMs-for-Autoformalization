import Mathlib.Logic.Function.Basic
namespace Function
variable {α : Type*} {β : Type*} {γ : Type*}
def Semiconj (f : α → β) (ga : α → α) (gb : β → β) : Prop :=
  ∀ x, f (ga x) = gb (f x)
namespace Semiconj
variable {f fab : α → β} {fbc : β → γ} {ga ga' : α → α} {gb gb' : β → β} {gc : γ → γ}
lemma _root_.Function.semiconj_iff_comp_eq : Semiconj f ga gb ↔ f ∘ ga = gb ∘ f := funext_iff.symm
protected alias ⟨comp_eq, _⟩ := semiconj_iff_comp_eq
protected theorem eq (h : Semiconj f ga gb) (x : α) : f (ga x) = gb (f x) :=
  h x
theorem comp_right (h : Semiconj f ga gb) (h' : Semiconj f ga' gb') :
    Semiconj f (ga ∘ ga') (gb ∘ gb') := fun x ↦ by
  simp only [comp_apply, h.eq, h'.eq]
protected theorem trans (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc) :
    Semiconj (fbc ∘ fab) ga gc := fun x ↦ by
  simp only [comp_apply, hab.eq, hbc.eq]
theorem comp_left (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb) :
    Semiconj (fbc ∘ fab) ga gc :=
  hab.trans hbc
theorem id_right : Semiconj f id id := fun _ ↦ rfl
theorem id_left : Semiconj id ga ga := fun _ ↦ rfl
theorem inverses_right (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : LeftInverse gb' gb) :
    Semiconj f ga' gb' := fun x ↦ by
  rw [← hb (f (ga' x)), ← h.eq, ha x]
lemma inverse_left {f' : β → α} (h : Semiconj f ga gb)
    (hf₁ : LeftInverse f' f) (hf₂ : RightInverse f' f) : Semiconj f' gb ga := fun x ↦ by
  rw [← hf₁.injective.eq_iff, h, hf₂, hf₂]
theorem option_map {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) :
    Semiconj (Option.map f) (Option.map ga) (Option.map gb)
  | none => rfl
  | some _ => congr_arg some <| h _
end Semiconj
protected def Commute (f g : α → α) : Prop :=
  Semiconj f g g
open Function (Commute)
theorem Semiconj.commute {f g : α → α} (h : Semiconj f g g) : Commute f g := h
namespace Commute
variable {f f' g g' : α → α}
theorem semiconj (h : Commute f g) : Semiconj f g g := h
@[refl]
theorem refl (f : α → α) : Commute f f := fun _ ↦ Eq.refl _
@[symm]
theorem symm (h : Commute f g) : Commute g f := fun x ↦ (h x).symm
theorem comp_right (h : Commute f g) (h' : Commute f g') : Commute f (g ∘ g') :=
  Semiconj.comp_right h h'
nonrec theorem comp_left (h : Commute f g) (h' : Commute f' g) : Commute (f ∘ f') g :=
  h.comp_left h'
theorem id_right : Commute f id := Semiconj.id_right
theorem id_left : Commute id f :=
  Semiconj.id_left
nonrec theorem option_map {f g : α → α} (h : Commute f g) : Commute (Option.map f) (Option.map g) :=
  h.option_map
end Commute
def Semiconj₂ (f : α → β) (ga : α → α → α) (gb : β → β → β) : Prop :=
  ∀ x y, f (ga x y) = gb (f x) (f y)
namespace Semiconj₂
variable {f : α → β} {ga : α → α → α} {gb : β → β → β}
protected theorem eq (h : Semiconj₂ f ga gb) (x y : α) : f (ga x y) = gb (f x) (f y) :=
  h x y
protected theorem comp_eq (h : Semiconj₂ f ga gb) : bicompr f ga = bicompl gb f f :=
  funext fun x ↦ funext <| h x
theorem id_left (op : α → α → α) : Semiconj₂ id op op := fun _ _ ↦ rfl
theorem comp {f' : β → γ} {gc : γ → γ → γ} (hf' : Semiconj₂ f' gb gc) (hf : Semiconj₂ f ga gb) :
    Semiconj₂ (f' ∘ f) ga gc := fun x y ↦ by simp only [hf'.eq, hf.eq, comp_apply]
theorem isAssociative_right [Std.Associative ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.Associative gb :=
  ⟨h_surj.forall₃.2 fun x₁ x₂ x₃ ↦ by simp only [← h.eq, Std.Associative.assoc (op := ga)]⟩
theorem isAssociative_left [Std.Associative gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.Associative ga :=
  ⟨fun x₁ x₂ x₃ ↦ h_inj <| by simp only [h.eq, Std.Associative.assoc (op := gb)]⟩
theorem isIdempotent_right [Std.IdempotentOp ga] (h : Semiconj₂ f ga gb) (h_surj : Surjective f) :
    Std.IdempotentOp gb :=
  ⟨h_surj.forall.2 fun x ↦ by simp only [← h.eq, Std.IdempotentOp.idempotent (op := ga)]⟩
theorem isIdempotent_left [Std.IdempotentOp gb] (h : Semiconj₂ f ga gb) (h_inj : Injective f) :
    Std.IdempotentOp ga :=
  ⟨fun x ↦ h_inj <| by rw [h.eq, Std.IdempotentOp.idempotent (op := gb)]⟩
end Semiconj₂
end Function