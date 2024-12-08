import Mathlib.Logic.Function.Basic
import Mathlib.Util.CompileInductive
protected def copy (f : MyHom A B) (f' : A → B) (h : f' = ⇑f) : MyHom A B where
  toFun := f'
  map_op' := h.symm ▸ f.map_op'
end MyHom
```
This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.
## Morphism classes extending `DFunLike` and `FunLike`
The `FunLike` design provides further benefits if you put in a bit more work.
The first step is to extend `FunLike` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:
```
class MyHomClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [FunLike F A B] : Prop :=
  (map_op : ∀ (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y))
@[simp]
lemma map_op {F A B : Type*} [MyClass A] [MyClass B] [FunLike F A B] [MyHomClass F A B]
    (f : F) (x y : A) :
    f (MyClass.op x y) = MyClass.op (f x) (f y) :=
  MyHomClass.map_op _ _ _
instance : MyHomClass (MyHom A B) A B where
  map_op := MyHom.map_op'
```
Note that `A B` are marked as `outParam` even though they are not purely required to be so
due to the `FunLike` parameter already filling them in. This is required to see through
type synonyms, which is important in the category theory library. Also, it appears having them as
`outParam` is slightly faster.
The second step is to add instances of your new `MyHomClass` for all types extending `MyHom`.
Typically, you can just declare a new class analogous to `MyHomClass`:
```
structure CoolerHom (A B : Type*) [CoolClass A] [CoolClass B] extends MyHom A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)
class CoolerHomClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
  [FunLike F A B] extends MyHomClass F A B :=
    (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)
@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B] [FunLike F A B]
    [CoolerHomClass F A B] (f : F) : f CoolClass.cool = CoolClass.cool :=
  CoolerHomClass.map_cool _
variable {A B : Type*} [CoolClass A] [CoolClass B]
instance : FunLike (CoolerHom A B) A B where
  coe f := f.toFun
  coe_injective' := fun f g h ↦ by cases f; cases g; congr; apply DFunLike.coe_injective; congr
instance : CoolerHomClass (CoolerHom A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'
```
Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
lemma do_something {F : Type*} [FunLike F A B] [MyHomClass F A B] (f : F) : sorry :=
  sorry
```
This means anything set up for `MyHom`s will automatically work for `CoolerHomClass`es,
and defining `CoolerHomClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyHom`-related declaration.
## Design rationale
The current form of FunLike was set up in pull request https://github.com/leanprover-community/mathlib4/pull/8386:
https://github.com/leanprover-community/mathlib4/pull/8386
We made `FunLike` *unbundled*: child classes don't extend `FunLike`, they take a `[FunLike F A B]`
parameter instead. This suits the instance synthesis algorithm better: it's easy to verify a type
does **not** have a `FunLike` instance by checking the discrimination tree once instead of searching
the entire `extends` hierarchy.
-/
@[notation_class * toFun Simps.findCoercionArgs]
class DFunLike (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α → Sort*) where
  coe : F → ∀ a : α, β a
  coe_injective' : Function.Injective coe
compile_def% DFunLike.coe
abbrev FunLike F α β := DFunLike F α fun _ => β
section Dependent
variable (F α : Sort*) (β : α → Sort*)
namespace DFunLike
variable {F α β} [i : DFunLike F α β]
instance (priority := 100) hasCoeToFun : CoeFun F (fun _ ↦ ∀ a : α, β a) where
  coe := @DFunLike.coe _ _ β _ 
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``DFunLike.coe
    (some { numArgs := 5, coercee := 4, type := .coeFun })
theorem coe_eq_coe_fn : (DFunLike.coe (F := F)) = (fun f => ↑f) := rfl
theorem coe_injective : Function.Injective (fun f : F ↦ (f : ∀ a : α, β a)) :=
  DFunLike.coe_injective'
@[simp]
theorem coe_fn_eq {f g : F} : (f : ∀ a : α, β a) = (g : ∀ a : α, β a) ↔ f = g :=
  ⟨fun h ↦ DFunLike.coe_injective' h, fun h ↦ by cases h; rfl⟩
theorem ext' {f g : F} (h : (f : ∀ a : α, β a) = (g : ∀ a : α, β a)) : f = g :=
  DFunLike.coe_injective' h
theorem ext'_iff {f g : F} : f = g ↔ (f : ∀ a : α, β a) = (g : ∀ a : α, β a) :=
  coe_fn_eq.symm
theorem ext (f g : F) (h : ∀ x : α, f x = g x) : f = g :=
  DFunLike.coe_injective' (funext h)
theorem ext_iff {f g : F} : f = g ↔ ∀ x, f x = g x :=
  coe_fn_eq.symm.trans funext_iff
protected theorem congr_fun {f g : F} (h₁ : f = g) (x : α) : f x = g x :=
  congr_fun (congr_arg _ h₁) x
theorem ne_iff {f g : F} : f ≠ g ↔ ∃ a, f a ≠ g a :=
  ext_iff.not.trans not_forall
theorem exists_ne {f g : F} (h : f ≠ g) : ∃ x, f x ≠ g x :=
  ne_iff.mp h
lemma subsingleton_cod [∀ a, Subsingleton (β a)] : Subsingleton F :=
  ⟨fun _ _ ↦ coe_injective <| Subsingleton.elim _ _⟩
end DFunLike
end Dependent
section NonDependent
variable {F α β : Sort*} [i : FunLike F α β]
namespace DFunLike
protected theorem congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
  congr (congr_arg _ h₁) h₂
protected theorem congr_arg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
  congr_arg _ h₂
end DFunLike
end NonDependent