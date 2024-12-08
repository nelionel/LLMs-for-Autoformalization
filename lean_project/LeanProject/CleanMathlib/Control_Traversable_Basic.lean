import Mathlib.Data.Option.Defs
import Mathlib.Control.Functor
import Batteries.Data.List.Basic
import Mathlib.Control.Basic
open Function hiding comp
universe u v w
section ApplicativeTransformation
variable (F : Type u → Type v) [Applicative F]
variable (G : Type u → Type w) [Applicative G]
structure ApplicativeTransformation : Type max (u + 1) v w where
  app : ∀ α : Type u, F α → G α
  preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x
  preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y
end ApplicativeTransformation
namespace ApplicativeTransformation
variable (F : Type u → Type v) [Applicative F]
variable (G : Type u → Type w) [Applicative G]
instance : CoeFun (ApplicativeTransformation F G) fun _ => ∀ {α}, F α → G α :=
  ⟨fun η ↦ η.app _⟩
variable {F G}
theorem app_eq_coe (η : ApplicativeTransformation F G) : η.app = η :=
  rfl
@[simp]
theorem coe_mk (f : ∀ α : Type u, F α → G α) (pp ps) :
    (ApplicativeTransformation.mk f @pp @ps) = f :=
  rfl
protected theorem congr_fun (η η' : ApplicativeTransformation F G) (h : η = η') {α : Type u}
    (x : F α) : η x = η' x :=
  congrArg (fun η'' : ApplicativeTransformation F G => η'' x) h
protected theorem congr_arg (η : ApplicativeTransformation F G) {α : Type u} {x y : F α}
    (h : x = y) : η x = η y :=
  congrArg (fun z : F α => η z) h
theorem coe_inj ⦃η η' : ApplicativeTransformation F G⦄ (h : (η : ∀ α, F α → G α) = η') :
    η = η' := by
  cases η
  cases η'
  congr
@[ext]
theorem ext ⦃η η' : ApplicativeTransformation F G⦄ (h : ∀ (α : Type u) (x : F α), η x = η' x) :
    η = η' := by
  apply coe_inj
  ext1 α
  exact funext (h α)
section Preserves
variable (η : ApplicativeTransformation F G)
@[functor_norm]
theorem preserves_pure {α} : ∀ x : α, η (pure x) = pure x :=
  η.preserves_pure'
@[functor_norm]
theorem preserves_seq {α β : Type u} : ∀ (x : F (α → β)) (y : F α), η (x <*> y) = η x <*> η y :=
  η.preserves_seq'
variable [LawfulApplicative F] [LawfulApplicative G]
@[functor_norm]
theorem preserves_map {α β} (x : α → β) (y : F α) : η (x <$> y) = x <$> η y := by
  rw [← pure_seq, η.preserves_seq, preserves_pure, pure_seq]
theorem preserves_map' {α β} (x : α → β) : @η _ ∘ Functor.map x = Functor.map x ∘ @η _ := by
  ext y
  exact preserves_map η x y
end Preserves
def idTransformation : ApplicativeTransformation F F where
  app _ := id
  preserves_pure' := by simp
  preserves_seq' x y := by simp
instance : Inhabited (ApplicativeTransformation F F) :=
  ⟨idTransformation⟩
universe s t
variable {H : Type u → Type s} [Applicative H]
def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
    ApplicativeTransformation F H where
  app _ x := η' (η x)
  preserves_pure' x := by simp only [preserves_pure]
  preserves_seq' x y := by simp only [preserves_seq]
@[simp]
theorem comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
    {α : Type u} (x : F α) : η'.comp η x = η' (η x) :=
  rfl
theorem comp_assoc {I : Type u → Type t} [Applicative I]
    (η'' : ApplicativeTransformation H I) (η' : ApplicativeTransformation G H)
    (η : ApplicativeTransformation F G) : (η''.comp η').comp η = η''.comp (η'.comp η) :=
  rfl
@[simp]
theorem comp_id (η : ApplicativeTransformation F G) : η.comp idTransformation = η :=
  ext fun _ _ => rfl
@[simp]
theorem id_comp (η : ApplicativeTransformation F G) : idTransformation.comp η = η :=
  ext fun _ _ => rfl
end ApplicativeTransformation
open ApplicativeTransformation
class Traversable (t : Type u → Type u) extends Functor t where
  traverse : ∀ {m : Type u → Type u} [Applicative m] {α β}, (α → m β) → t α → m (t β)
open Functor
export Traversable (traverse)
section Functions
variable {t : Type u → Type u}
variable {α : Type u}
variable {f : Type u → Type u} [Applicative f]
def sequence [Traversable t] : t (f α) → f (t α) :=
  traverse id
end Functions
class LawfulTraversable (t : Type u → Type u) [Traversable t] extends LawfulFunctor t :
    Prop where
  id_traverse : ∀ {α} (x : t α), traverse (pure : α → Id α) x = x
  comp_traverse :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α β γ}
      (f : β → F γ) (g : α → G β) (x : t α),
      traverse (Functor.Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))
  traverse_eq_map_id : ∀ {α β} (f : α → β) (x : t α),
    traverse ((pure : β → Id β) ∘ f) x = id.mk (f <$> x)
  naturality :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      (η : ApplicativeTransformation F G) {α β} (f : α → F β) (x : t α),
      η (traverse f x) = traverse (@η _ ∘ f) x
instance : Traversable Id :=
  ⟨id⟩
instance : LawfulTraversable Id where
  id_traverse _ := rfl
  comp_traverse _ _ _ := rfl
  traverse_eq_map_id _ _ := rfl
  naturality _ _ _ _ _ := rfl
section
instance : Traversable Option :=
  ⟨Option.traverse⟩
instance : Traversable List :=
  ⟨List.traverse⟩
end
namespace Sum
variable {σ : Type u}
variable {F : Type u → Type u}
variable [Applicative F]
protected def traverse {α β} (f : α → F β) : σ ⊕ α → F (σ ⊕ β)
  | Sum.inl x => pure (Sum.inl x)
  | Sum.inr x => Sum.inr <$> f x
end Sum
instance {σ : Type u} : Traversable.{u} (Sum σ) :=
  ⟨@Sum.traverse _⟩