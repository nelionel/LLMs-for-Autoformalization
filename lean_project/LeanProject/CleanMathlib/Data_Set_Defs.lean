import Mathlib.Init
import Batteries.Util.ExtendedBinder
import Lean.Elab.Term
open Lean Elab Term Meta Batteries.ExtendedBinder
universe u
variable {α : Type u}
def Set (α : Type u) := α → Prop
def setOf {α : Type u} (p : α → Prop) : Set α :=
  p
namespace Set
protected def Mem (s : Set α) (a : α) : Prop :=
  s a
instance : Membership α (Set α) :=
  ⟨Set.Mem⟩
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x ↦ propext (h x))
protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
instance : LE (Set α) :=
  ⟨Set.Subset⟩
instance : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩
instance : EmptyCollection (Set α) :=
  ⟨fun _ ↦ False⟩
end Set
namespace Mathlib.Meta
syntax (name := setBuilder) "{" extBinder " | " term "}" : term
@[term_elab setBuilder]
def elabSetBuilder : TermElab
  | `({ $x:ident | $p }), expectedType? => do
    elabTerm (← `(setOf fun $x:ident ↦ $p)) expectedType?
  | `({ $x:ident : $t | $p }), expectedType? => do
    elabTerm (← `(setOf fun $x:ident : $t ↦ $p)) expectedType?
  | `({ $x:ident $b:binderPred | $p }), expectedType? => do
    elabTerm (← `(setOf fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)) expectedType?
  | _, _ => throwUnsupportedSyntax
@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()
open Batteries.ExtendedBinder in
macro (priority := low) "{" t:term " | " bs:extBinders "}" : term =>
  `({x | ∃ᵉ $bs:extBinders, $t = x})
macro (name := macroPattSetBuilder) (priority := low-1)
  "{" pat:term " : " t:term " | " p:term "}" : term =>
  `({ x : $t | match x with | $pat => $p })
@[inherit_doc macroPattSetBuilder]
macro (priority := low-1) "{" pat:term " | " p:term "}" : term =>
  `({ x | match x with | $pat => $p })
@[app_unexpander setOf]
def setOfPatternMatchUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term | $p:term })
      else
        throw ()
  | `($_ fun ($x:ident : $ty:term) ↦ match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term : $ty:term | $p:term })
      else
        throw ()
  | _ => throw ()
end Mathlib.Meta
namespace Set
def univ : Set α := {_a | True}
protected def insert (a : α) (s : Set α) : Set α := {b | b = a ∨ b ∈ s}
instance : Insert α (Set α) := ⟨Set.insert⟩
protected def singleton (a : α) : Set α := {b | b = a}
instance instSingletonSet : Singleton α (Set α) := ⟨Set.singleton⟩
protected def union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}
instance : Union (Set α) := ⟨Set.union⟩
protected def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}
instance : Inter (Set α) := ⟨Set.inter⟩
protected def compl (s : Set α) : Set α := {a | a ∉ s}
protected def diff (s t : Set α) : Set α := {a ∈ s | a ∉ t}
instance : SDiff (Set α) := ⟨Set.diff⟩
def powerset (s : Set α) : Set (Set α) := {t | t ⊆ s}
@[inherit_doc] prefix:100 "𝒫" => powerset
universe v in
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}
instance : Functor Set where map := @Set.image
instance : LawfulFunctor Set where
  id_map _ := funext fun _ ↦ propext ⟨fun ⟨_, sb, rfl⟩ ↦ sb, fun sb ↦ ⟨_, sb, rfl⟩⟩
  comp_map g h _ := funext <| fun c ↦ propext
    ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ ↦ ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     fun ⟨_, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ ↦ ⟨a, ⟨h₁, show h (g a) = c from h₂ ▸ h₃⟩⟩⟩
  map_const := rfl
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
end Set