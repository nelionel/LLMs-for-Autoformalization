import Mathlib.Logic.IsEmpty
import Mathlib.Tactic.Inhabit
universe u v w
@[ext]
structure Unique (α : Sort u) extends Inhabited α where
  uniq : ∀ a : α, a = default
attribute [class] Unique
attribute [nolint simpNF] Unique.mk.injEq
theorem unique_iff_exists_unique (α : Sort u) : Nonempty (Unique α) ↔ ∃! _ : α, True :=
  ⟨fun ⟨u⟩ ↦ ⟨u.default, trivial, fun a _ ↦ u.uniq a⟩,
   fun ⟨a, _, h⟩ ↦ ⟨⟨⟨a⟩, fun _ ↦ h _ trivial⟩⟩⟩
theorem unique_subtype_iff_exists_unique {α} (p : α → Prop) :
    Nonempty (Unique (Subtype p)) ↔ ∃! a, p a :=
  ⟨fun ⟨u⟩ ↦ ⟨u.default.1, u.default.2, fun a h ↦ congr_arg Subtype.val (u.uniq ⟨a, h⟩)⟩,
   fun ⟨a, ha, he⟩ ↦ ⟨⟨⟨⟨a, ha⟩⟩, fun ⟨b, hb⟩ ↦ by
      congr
      exact he b hb⟩⟩⟩
abbrev uniqueOfSubsingleton {α : Sort*} [Subsingleton α] (a : α) : Unique α where
  default := a
  uniq _ := Subsingleton.elim _ _
instance PUnit.unique : Unique PUnit.{u} where
  default := PUnit.unit
  uniq x := subsingleton x _
@[simp, nolint simpNF]
theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit :=
  rfl
def uniqueProp {p : Prop} (h : p) : Unique.{0} p where
  default := h
  uniq _ := rfl
instance : Unique True :=
  uniqueProp trivial
namespace Unique
open Function
section
variable {α : Sort*} [Unique α]
instance (priority := 100) : Inhabited α :=
  toInhabited ‹Unique α›
theorem eq_default (a : α) : a = default :=
  uniq _ a
theorem default_eq (a : α) : default = a :=
  (uniq _ a).symm
instance (priority := 100) instSubsingleton : Subsingleton α :=
  subsingleton_of_forall_eq _ eq_default
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ p default :=
  ⟨fun h ↦ h _, fun h x ↦ by rwa [Unique.eq_default x]⟩
theorem exists_iff {p : α → Prop} : Exists p ↔ p default :=
  ⟨fun ⟨a, ha⟩ ↦ eq_default a ▸ ha, Exists.intro default⟩
end
variable {α : Sort*}
@[ext]
protected theorem subsingleton_unique' : ∀ h₁ h₂ : Unique α, h₁ = h₂
  | ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ => by congr; rw [h x, h y]
instance subsingleton_unique : Subsingleton (Unique α) :=
  ⟨Unique.subsingleton_unique'⟩
abbrev mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun _ ↦ Subsingleton.elim _ _ }
end Unique
theorem nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty α] : Nonempty (Unique α) := by
  inhabit α
  exact ⟨Unique.mk' α⟩
theorem unique_iff_subsingleton_and_nonempty (α : Sort u) :
    Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α :=
  ⟨fun ⟨u⟩ ↦ by constructor <;> exact inferInstance,
   fun ⟨hs, hn⟩ ↦ nonempty_unique α⟩
variable {α : Sort*}
@[simp]
theorem Pi.default_def {β : α → Sort v} [∀ a, Inhabited (β a)] :
    @default (∀ a, β a) _ = fun a : α ↦ @default (β a) _ :=
  rfl
theorem Pi.default_apply {β : α → Sort v} [∀ a, Inhabited (β a)] (a : α) :
    @default (∀ a, β a) _ a = default :=
  rfl
instance Pi.unique {β : α → Sort v} [∀ a, Unique (β a)] : Unique (∀ a, β a) where
  uniq := fun _ ↦ funext fun _ ↦ Unique.eq_default _
instance Pi.uniqueOfIsEmpty [IsEmpty α] (β : α → Sort v) : Unique (∀ a, β a) where
  default := isEmptyElim
  uniq _ := funext isEmptyElim
theorem eq_const_of_subsingleton {β : Sort*} [Subsingleton α] (f : α → β) (a : α) :
    f = Function.const α (f a) :=
  funext fun x ↦ Subsingleton.elim x a ▸ rfl
theorem eq_const_of_unique {β : Sort*} [Unique α] (f : α → β) : f = Function.const α (f default) :=
  eq_const_of_subsingleton ..
theorem heq_const_of_unique [Unique α] {β : α → Sort v} (f : ∀ a, β a) :
    HEq f (Function.const α (f default)) :=
  (Function.hfunext rfl) fun i _ _ ↦ by rw [Subsingleton.elim i default]; rfl
namespace Function
variable {β : Sort*} {f : α → β}
protected theorem Injective.subsingleton (hf : Injective f) [Subsingleton β] : Subsingleton α :=
  ⟨fun _ _ ↦ hf <| Subsingleton.elim _ _⟩
protected theorem Surjective.subsingleton [Subsingleton α] (hf : Surjective f) : Subsingleton β :=
  ⟨hf.forall₂.2 fun x y ↦ congr_arg f <| Subsingleton.elim x y⟩
protected def Surjective.unique {α : Sort u} (f : α → β) (hf : Surjective f) [Unique.{u} α] :
    Unique β :=
  @Unique.mk' _ ⟨f default⟩ hf.subsingleton
protected def Injective.unique [Inhabited α] [Subsingleton β] (hf : Injective f) : Unique α :=
  @Unique.mk' _ _ hf.subsingleton
def Surjective.uniqueOfSurjectiveConst (α : Type*) {β : Type*} (b : β)
    (h : Function.Surjective (Function.const α b)) : Unique β :=
  @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ ↦ rfl) b
end Function
section Pi
variable {ι : Sort*} {α : ι → Sort*}
def uniqueElim [Unique ι] (x : α (default : ι)) (i : ι) : α i := by
  rw [Unique.eq_default i]
  exact x
@[simp]
theorem uniqueElim_default {_ : Unique ι} (x : α (default : ι)) : uniqueElim x (default : ι) = x :=
  rfl
@[simp]
theorem uniqueElim_const {β : Sort*} {_ : Unique ι} (x : β) (i : ι) :
    uniqueElim (α := fun _ ↦ β) x i = x :=
  rfl
end Pi
attribute [local simp] eq_iff_true_of_subsingleton in
theorem Unique.bijective {A B} [Unique A] [Unique B] {f : A → B} : Function.Bijective f := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨default, ?_, ?_⟩ <;> intro x <;> simp
namespace Option
theorem subsingleton_iff_isEmpty {α : Type u} : Subsingleton (Option α) ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ Option.noConfusion <| @Subsingleton.elim _ h x none⟩,
   fun h ↦ ⟨fun x y ↦
     Option.casesOn x (Option.casesOn y rfl fun x ↦ h.elim x) fun x ↦ h.elim x⟩⟩
instance {α} [IsEmpty α] : Unique (Option α) :=
  @Unique.mk' _ _ (subsingleton_iff_isEmpty.2 ‹_›)
end Option
section Subtype
instance Unique.subtypeEq (y : α) : Unique { x // x = y } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ ↦ by congr
instance Unique.subtypeEq' (y : α) : Unique { x // y = x } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ ↦ by subst hx; congr
end Subtype
instance Fin.instUnique : Unique (Fin 1) where uniq _ := Subsingleton.elim _ _