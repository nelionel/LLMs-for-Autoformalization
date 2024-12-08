import Mathlib.Control.Traversable.Lemmas
import Mathlib.Logic.Equiv.Defs
universe u
namespace Equiv
section Functor
variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)
variable [Functor t]
open Functor
protected def map {α β : Type u} (f : α → β) (x : t' α) : t' β :=
  eqv β <| map f ((eqv α).symm x)
protected def functor : Functor t' where map := Equiv.map eqv
variable [LawfulFunctor t]
protected theorem id_map {α : Type u} (x : t' α) : Equiv.map eqv id x = x := by
  simp [Equiv.map, id_map]
protected theorem comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
    Equiv.map eqv (h ∘ g) x = Equiv.map eqv h (Equiv.map eqv g x) := by
  simp [Equiv.map, Function.comp_def]
protected theorem lawfulFunctor : @LawfulFunctor _ (Equiv.functor eqv) :=
  let _inst := Equiv.functor eqv; {
    map_const := fun {_ _} => rfl
    id_map := Equiv.id_map eqv
    comp_map := Equiv.comp_map eqv }
protected theorem lawfulFunctor' [F : Functor t']
    (h₀ : ∀ {α β} (f : α → β), Functor.map f = Equiv.map eqv f)
    (h₁ : ∀ {α β} (f : β), Functor.mapConst f = (Equiv.map eqv ∘ Function.const α) f) :
    LawfulFunctor t' := by
  have : F = Equiv.functor eqv := by
    cases F
    dsimp [Equiv.functor]
    congr <;> ext <;> dsimp only <;> [rw [← h₀]; rw [← h₁]] <;> rfl
  subst this
  exact Equiv.lawfulFunctor eqv
end Functor
section Traversable
variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)
variable [Traversable t]
variable {m : Type u → Type u} [Applicative m]
variable {α β : Type u}
protected def traverse (f : α → m β) (x : t' α) : m (t' β) :=
  eqv β <$> traverse f ((eqv α).symm x)
theorem traverse_def (f : α → m β) (x : t' α) :
    Equiv.traverse eqv f x = eqv β <$> traverse f ((eqv α).symm x) :=
  rfl
protected def traversable : Traversable t' where
  toFunctor := Equiv.functor eqv
  traverse := Equiv.traverse eqv
end Traversable
section Equiv
variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)
variable [Traversable t] [LawfulTraversable t]
variable {F G : Type u → Type u} [Applicative F] [Applicative G]
variable [LawfulApplicative F] [LawfulApplicative G]
variable (η : ApplicativeTransformation F G)
variable {α β γ : Type u}
open LawfulTraversable Functor
protected theorem id_traverse (x : t' α) : Equiv.traverse eqv (pure : α → Id α) x = x := by
  rw [Equiv.traverse, id_traverse, Id.map_eq, apply_symm_apply]
protected theorem traverse_eq_map_id (f : α → β) (x : t' α) :
    Equiv.traverse eqv ((pure : β → Id β) ∘ f) x = pure (Equiv.map eqv f x) := by
  simp only [Equiv.traverse, traverse_eq_map_id, Id.map_eq, Id.pure_eq]; rfl
protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : t' α) :
    Equiv.traverse eqv (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Equiv.traverse eqv f <$> Equiv.traverse eqv g x) := by
  rw [traverse_def, comp_traverse, Comp.map_mk]
  simp only [map_map, Function.comp_def, traverse_def, symm_apply_apply]
protected theorem naturality (f : α → F β) (x : t' α) :
    η (Equiv.traverse eqv f x) = Equiv.traverse eqv (@η _ ∘ f) x := by
  simp only [Equiv.traverse, functor_norm]
protected theorem isLawfulTraversable : @LawfulTraversable t' (Equiv.traversable eqv) :=
  let _inst := Equiv.traversable eqv; {
    toLawfulFunctor := Equiv.lawfulFunctor eqv
    id_traverse := Equiv.id_traverse eqv
    comp_traverse := Equiv.comp_traverse eqv
    traverse_eq_map_id := Equiv.traverse_eq_map_id eqv
    naturality := Equiv.naturality eqv }
protected theorem isLawfulTraversable' [Traversable t']
    (h₀ : ∀ {α β} (f : α → β), map f = Equiv.map eqv f)
    (h₁ : ∀ {α β} (f : β), mapConst f = (Equiv.map eqv ∘ Function.const α) f)
    (h₂ : ∀ {F : Type u → Type u} [Applicative F],
      ∀ [LawfulApplicative F] {α β} (f : α → F β), traverse f = Equiv.traverse eqv f) :
    LawfulTraversable t' where
  toLawfulFunctor := Equiv.lawfulFunctor' eqv @h₀ @h₁
  id_traverse _ := by rw [h₂, Equiv.id_traverse]
  comp_traverse _ _ _ := by rw [h₂, Equiv.comp_traverse, h₂]; congr; rw [h₂]
  traverse_eq_map_id _ _ := by rw [h₂, Equiv.traverse_eq_map_id, h₀]; rfl
  naturality _ _ _ _ _ := by rw [h₂, Equiv.naturality, h₂]
end Equiv
end Equiv