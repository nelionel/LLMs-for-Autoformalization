import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Eqns
import Mathlib.Tactic.TypeStar
import Batteries.Logic
universe u₁ u₂ u₃ u₄ u₅
namespace Function
variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₅}
lemma flip_def {f : α → β → φ} : flip f = fun b a => f a b := rfl
#adaptation_note 
@[inline, reducible]
def dcomp {β : α → Sort u₂} {φ : ∀ {x : α}, β x → Sort u₃} (f : ∀ {x : α} (y : β x), φ y)
    (g : ∀ x, β x) : ∀ x, φ (g x) := fun x => f (g x)
infixr:80 " ∘' " => Function.dcomp
abbrev onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)
@[inherit_doc onFun]
infixl:2 " on " => onFun
abbrev swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y
#adaptation_note 
theorem swap_def {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : swap f = fun y x => f x y := rfl
@[simp, mfld_simps]
theorem id_comp (f : α → β) : id ∘ f = f := rfl
@[simp, mfld_simps]
theorem comp_id (f : α → β) : f ∘ id = f := rfl
theorem comp_assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl
@[deprecated (since := "2024-09-24")] alias comp.assoc := comp_assoc
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
theorem Injective.comp {g : β → φ} {f : α → β} (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := fun _a₁ _a₂ => fun h => hf (hg h)
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b
theorem Surjective.comp {g : β → φ} {f : α → β} (hg : Surjective g) (hf : Surjective f) :
    Surjective (g ∘ f) := fun c : φ =>
  Exists.elim (hg c) fun b hb =>
    Exists.elim (hf b) fun a ha =>
      Exists.intro a (show g (f a) = c from Eq.trans (congr_arg g ha) hb)
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩
def LeftInverse (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x
def HasLeftInverse (f : α → β) : Prop :=
  ∃ finv : β → α, LeftInverse finv f
def RightInverse (g : β → α) (f : α → β) : Prop :=
  LeftInverse f g
def HasRightInverse (f : α → β) : Prop :=
  ∃ finv : β → α, RightInverse finv f
theorem LeftInverse.injective {g : β → α} {f : α → β} : LeftInverse g f → Injective f :=
  fun h a b faeqfb =>
  calc
    a = g (f a) := (h a).symm
    _ = g (f b) := congr_arg g faeqfb
    _ = b := h b
theorem HasLeftInverse.injective {f : α → β} : HasLeftInverse f → Injective f := fun h =>
  Exists.elim h fun _finv inv => inv.injective
theorem rightInverse_of_injective_of_leftInverse {f : α → β} {g : β → α} (injf : Injective f)
    (lfg : LeftInverse f g) : RightInverse f g := fun x =>
  have h : f (g (f x)) = f x := lfg (f x)
  injf h
theorem RightInverse.surjective {f : α → β} {g : β → α} (h : RightInverse g f) : Surjective f :=
  fun y => ⟨g y, h y⟩
theorem HasRightInverse.surjective {f : α → β} : HasRightInverse f → Surjective f
  | ⟨_finv, inv⟩ => inv.surjective
theorem leftInverse_of_surjective_of_rightInverse {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx =>
    calc
      f (g y) = f (g (f x)) := hx ▸ rfl
      _ = f x := Eq.symm (rfg x) ▸ rfl
      _ = y := hx
theorem injective_id : Injective (@id α) := fun _a₁ _a₂ h => h
theorem surjective_id : Surjective (@id α) := fun a => ⟨a, rfl⟩
theorem bijective_id : Bijective (@id α) :=
  ⟨injective_id, surjective_id⟩
end Function
namespace Function
variable {α : Type u₁} {β : Type u₂}
protected theorem LeftInverse.id {g : β → α} {f : α → β} (h : LeftInverse g f) : g ∘ f = id :=
  funext h
protected theorem RightInverse.id {g : β → α} {f : α → β} (h : RightInverse g f) : f ∘ g = id :=
  funext h
def IsFixedPt (f : α → α) (x : α) := f x = x
end Function
namespace Pi
variable {ι : Sort*} {α β : ι → Sort*}
protected def map (f : ∀ i, α i → β i) : (∀ i, α i) → (∀ i, β i) := fun a i ↦ f i (a i)
@[simp]
lemma map_apply (f : ∀ i, α i → β i) (a : ∀ i, α i) (i : ι) : Pi.map f a i = f i (a i) := rfl
end Pi