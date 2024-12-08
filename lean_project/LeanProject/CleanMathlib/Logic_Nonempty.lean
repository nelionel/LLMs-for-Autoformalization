import Mathlib.Algebra.Group.ZeroOne
import Mathlib.Logic.Function.Defs
section
variable {α β : Sort*}
@[simp]
theorem Nonempty.forall {α} {p : Nonempty α → Prop} : (∀ h : Nonempty α, p h) ↔ ∀ a, p ⟨a⟩ :=
  Iff.intro (fun h _ ↦ h _) fun h ⟨a⟩ ↦ h a
@[simp]
theorem Nonempty.exists {α} {p : Nonempty α → Prop} : (∃ h : Nonempty α, p h) ↔ ∃ a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ ↦ ⟨a, h⟩) fun ⟨a, h⟩ ↦ ⟨⟨a⟩, h⟩
theorem exists_true_iff_nonempty {α : Sort*} : (∃ _ : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨a, trivial⟩
@[deprecated (since := "2024-08-30")] alias nonempty_Prop := nonempty_prop
theorem Nonempty.imp {α} {p : Prop} : (Nonempty α → p) ↔ (α → p) :=
  Nonempty.forall
theorem not_nonempty_iff_imp_false {α : Sort*} : ¬Nonempty α ↔ α → False :=
  Nonempty.imp
@[simp]
theorem nonempty_psigma {α} {β : α → Sort*} : Nonempty (PSigma β) ↔ ∃ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ ↦ ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ ↦ ⟨⟨a, c⟩⟩
@[simp]
theorem nonempty_subtype {α} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ ↦ ⟨a, h⟩) fun ⟨a, h⟩ ↦ ⟨⟨a, h⟩⟩
@[simp]
theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ ↦ ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ ↦ ⟨⟨a, b⟩⟩
@[simp]
theorem nonempty_psum {α β} : Nonempty (α ⊕' β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ ↦
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h ↦
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩
@[simp]
theorem nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨⟨a⟩⟩
noncomputable def Classical.inhabited_of_nonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩
protected noncomputable abbrev Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h
protected noncomputable abbrev Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h
theorem Nonempty.map {α β} (f : α → β) : Nonempty α → Nonempty β
  | ⟨h⟩ => ⟨f h⟩
protected theorem Nonempty.map2 {α β γ : Sort*} (f : α → β → γ) :
    Nonempty α → Nonempty β → Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩
protected theorem Nonempty.congr {α β} (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩
theorem Nonempty.elim_to_inhabited {α : Sort*} [h : Nonempty α] {p : Prop} (f : Inhabited α → p) :
    p :=
  h.elim <| f ∘ Inhabited.mk
theorem Classical.nonempty_pi {ι} {α : ι → Sort*} : Nonempty (∀ i, α i) ↔ ∀ i, Nonempty (α i) :=
  ⟨fun ⟨f⟩ a ↦ ⟨f a⟩, @Pi.instNonempty _ _⟩
theorem subsingleton_of_not_nonempty {α : Sort*} (h : ¬Nonempty α) : Subsingleton α :=
  ⟨fun x ↦ False.elim <| not_nonempty_iff_imp_false.mp h x⟩
theorem Function.Surjective.nonempty [h : Nonempty β] {f : α → β} (hf : Function.Surjective f) :
    Nonempty α :=
  let ⟨y⟩ := h
  let ⟨x, _⟩ := hf y
  ⟨x⟩
end
section
variable {α β : Type*} {γ : α → Type*}
instance (priority := 20) Zero.instNonempty [Zero α] : Nonempty α :=
  ⟨0⟩
instance (priority := 20) One.instNonempty [One α] : Nonempty α :=
  ⟨1⟩
@[simp]
theorem nonempty_sigma : Nonempty (Σa : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ ↦ ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ ↦ ⟨⟨a, c⟩⟩
@[simp]
theorem nonempty_sum : Nonempty (α ⊕ β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ ↦
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h ↦
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩
@[simp]
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ ↦ ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ ↦ ⟨⟨a, b⟩⟩
@[simp]
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨⟨a⟩⟩
end