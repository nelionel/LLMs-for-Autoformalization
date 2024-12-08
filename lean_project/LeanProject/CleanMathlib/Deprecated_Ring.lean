import Mathlib.Deprecated.Group
universe u v
variable {α : Type u}
structure IsSemiringHom {α : Type u} {β : Type v} [Semiring α] [Semiring β] (f : α → β) : Prop where
  map_zero : f 0 = 0
  map_one : f 1 = 1
  map_add : ∀ x y, f (x + y) = f x + f y
  map_mul : ∀ x y, f (x * y) = f x * f y
namespace IsSemiringHom
variable {β : Type v} [Semiring α] [Semiring β]
variable {f : α → β}
theorem id : IsSemiringHom (@id α) := by constructor <;> intros <;> rfl
theorem comp (hf : IsSemiringHom f) {γ} [Semiring γ] {g : β → γ} (hg : IsSemiringHom g) :
    IsSemiringHom (g ∘ f) :=
  { map_zero := by simpa [map_zero hf] using map_zero hg
    map_one := by simpa [map_one hf] using map_one hg
    map_add := fun {x y} => by simp [map_add hf, map_add hg]
    map_mul := fun {x y} => by simp [map_mul hf, map_mul hg] }
theorem to_isAddMonoidHom (hf : IsSemiringHom f) : IsAddMonoidHom f :=
  { ‹IsSemiringHom f› with map_add := by apply @‹IsSemiringHom f›.map_add }
theorem to_isMonoidHom (hf : IsSemiringHom f) : IsMonoidHom f :=
  { ‹IsSemiringHom f› with }
end IsSemiringHom
structure IsRingHom {α : Type u} {β : Type v} [Ring α] [Ring β] (f : α → β) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ x y, f (x * y) = f x * f y
  map_add : ∀ x y, f (x + y) = f x + f y
namespace IsRingHom
variable {β : Type v} [Ring α] [Ring β]
theorem of_semiring {f : α → β} (H : IsSemiringHom f) : IsRingHom f :=
  { H with }
variable {f : α → β} {x y : α}
theorem map_zero (hf : IsRingHom f) : f 0 = 0 :=
  calc
    f 0 = f (0 + 0) - f 0 := by rw [hf.map_add]; simp
    _ = 0 := by simp
theorem map_neg (hf : IsRingHom f) : f (-x) = -f x :=
  calc
    f (-x) = f (-x + x) - f x := by rw [hf.map_add]; simp
    _ = -f x := by simp [hf.map_zero]
theorem map_sub (hf : IsRingHom f) : f (x - y) = f x - f y := by
  simp [sub_eq_add_neg, hf.map_add, hf.map_neg]
theorem id : IsRingHom (@id α) := by constructor <;> intros <;> rfl
theorem comp (hf : IsRingHom f) {γ} [Ring γ] {g : β → γ} (hg : IsRingHom g) : IsRingHom (g ∘ f) :=
  { map_add := fun x y => by simp only [Function.comp_apply, map_add hf, map_add hg]
    map_mul := fun x y => by simp only [Function.comp_apply, map_mul hf, map_mul hg]
    map_one := by simp only [Function.comp_apply, map_one hf, map_one hg] }
theorem to_isSemiringHom (hf : IsRingHom f) : IsSemiringHom f :=
  { ‹IsRingHom f› with map_zero := map_zero hf }
theorem to_isAddGroupHom (hf : IsRingHom f) : IsAddGroupHom f :=
  { map_add := hf.map_add }
end IsRingHom
variable {β : Type v} {rα : Semiring α} {rβ : Semiring β}
namespace RingHom
section
def of {f : α → β} (hf : IsSemiringHom f) : α →+* β :=
  { MonoidHom.of hf.to_isMonoidHom, AddMonoidHom.of hf.to_isAddMonoidHom with toFun := f }
@[simp]
theorem coe_of {f : α → β} (hf : IsSemiringHom f) : ⇑(of hf) = f :=
  rfl
theorem to_isSemiringHom (f : α →+* β) : IsSemiringHom f :=
  { map_zero := f.map_zero
    map_one := f.map_one
    map_add := f.map_add
    map_mul := f.map_mul }
end
theorem to_isRingHom {α γ} [Ring α] [Ring γ] (g : α →+* γ) : IsRingHom g :=
  IsRingHom.of_semiring g.to_isSemiringHom
end RingHom