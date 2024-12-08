import Mathlib.Data.FunLike.Embedding
protected def copy (f : MyIso A B) (f' : A → B) (f_inv : B → A)
    (h₁ : f' = f) (h₂ : f_inv = f.invFun) : MyIso A B where
  toFun := f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'
end MyIso
```
This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.
## Isomorphism classes extending `EquivLike`
The `EquivLike` design provides further benefits if you put in a bit more work.
The first step is to extend `EquivLike` to create a class of those types satisfying
the axioms of your new type of isomorphisms.
Continuing the example above:
```
class MyIsoClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [EquivLike F A B]
    extends MyHomClass F A B
namespace MyIso
variable {A B : Type*} [MyClass A] [MyClass B]
instance : MyIsoClass (MyIso A B) A B where
  map_op := MyIso.map_op'
end MyIso
```
The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.
Typically, you can just declare a new class analogous to `MyIsoClass`:
```
structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B] extends MyIso A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)
class CoolerIsoClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [EquivLike F A B]
    extends MyIsoClass F A B where
  (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)
@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [EquivLike F A B] [CoolerIsoClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerIsoClass.map_cool _
namespace CoolerIso
variable {A B : Type*} [CoolClass A] [CoolClass B]
instance : EquivLike (CoolerIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂
instance : CoolerIsoClass (CoolerIso A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'
end CoolerIso
```
Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
lemma do_something {F : Type*} [EquivLike F A B] [MyIsoClass F A B] (f : F) : sorry := sorry
```
This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.
-/
class EquivLike (E : Sort*) (α β : outParam (Sort*)) where
  coe : E → α → β
  inv : E → β → α
  left_inv : ∀ e, Function.LeftInverse (inv e) (coe e)
  right_inv : ∀ e, Function.RightInverse (inv e) (coe e)
  coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g
namespace EquivLike
variable {E F α β γ : Sort*} [EquivLike E α β] [EquivLike F β γ]
theorem inv_injective : Function.Injective (EquivLike.inv : E → β → α) := fun e g h ↦
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h
instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E → α → β)
  coe_injective' e g h :=
    coe_injective' e g h ((left_inv e).eq_rightInverse (h.symm ▸ right_inv g))
instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  injective' e := (left_inv e).injective
protected theorem injective (e : E) : Function.Injective e :=
  EmbeddingLike.injective e
protected theorem surjective (e : E) : Function.Surjective e :=
  (right_inv e).surjective
protected theorem bijective (e : E) : Function.Bijective (e : α → β) :=
  ⟨EquivLike.injective e, EquivLike.surjective e⟩
theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f
@[simp]
theorem injective_comp (e : E) (f : β → γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)
@[simp]
theorem surjective_comp (e : E) (f : β → γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f
@[simp]
theorem bijective_comp (e : E) (f : β → γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f
@[simp]
theorem inv_apply_apply (e : E) (a : α) : EquivLike.inv e (e a) = a :=
  left_inv _ _
@[simp]
theorem apply_inv_apply (e : E) (b : β) : e (EquivLike.inv e b) = b :=
  right_inv _ _
lemma inv_apply_eq_iff_eq_apply {e : E} {b : β} {a : α} : (EquivLike.inv e b) = a ↔ b = e a := by
  constructor <;> rintro ⟨_, rfl⟩ <;> simp
theorem comp_injective (f : α → β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  EmbeddingLike.comp_injective f e
@[simp]
theorem comp_surjective (f : α → β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f
@[simp]
theorem comp_bijective (f : α → β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f
lemma subsingleton_dom [FunLike F β γ] [Subsingleton β] : Subsingleton F :=
  ⟨fun f g ↦ DFunLike.ext f g fun _ ↦ (right_inv f).injective <| Subsingleton.elim _ _⟩
end EquivLike