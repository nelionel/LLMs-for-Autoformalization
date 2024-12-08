import Mathlib.Order.CompleteLattice
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
noncomputable section
universe v u
open CategoryTheory
open CategoryTheory.Limits
namespace CategoryTheory
inductive Pairwise (ι : Type v)
  | single : ι → Pairwise ι
  | pair : ι → ι → Pairwise ι
variable {ι : Type v}
namespace Pairwise
instance pairwiseInhabited [Inhabited ι] : Inhabited (Pairwise ι) :=
  ⟨single default⟩
inductive Hom : Pairwise ι → Pairwise ι → Type v
  | id_single : ∀ i, Hom (single i) (single i)
  | id_pair : ∀ i j, Hom (pair i j) (pair i j)
  | left : ∀ i j, Hom (pair i j) (single i)
  | right : ∀ i j, Hom (pair i j) (single j)
open Hom
instance homInhabited [Inhabited ι] : Inhabited (Hom (single (default : ι)) (single default)) :=
  ⟨id_single default⟩
def id : ∀ o : Pairwise ι, Hom o o
  | single i => id_single i
  | pair i j => id_pair i j
def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃
  | _, _, _, id_single _, g => g
  | _, _, _, id_pair _ _, g => g
  | _, _, _, left i j, id_single _ => left i j
  | _, _, _, right i j, id_single _ => right i j
section
open Lean Elab Tactic in
def pairwiseCases : TacticM Unit := do
  evalTactic (← `(tactic| casesm* (_ : Pairwise _) ⟶ (_ : Pairwise _)))
attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] pairwiseCases in
instance : Category (Pairwise ι) where
  Hom := Hom
  id := id
  comp f g := comp f g
end
variable {α : Type v} (U : ι → α)
section
variable [SemilatticeInf α]
@[simp]
def diagramObj : Pairwise ι → α
  | single i => U i
  | pair i j => U i ⊓ U j
@[simp]
def diagramMap : ∀ {o₁ o₂ : Pairwise ι} (_ : o₁ ⟶ o₂), diagramObj U o₁ ⟶ diagramObj U o₂
  | _, _, id_single _ => 𝟙 _
  | _, _, id_pair _ _ => 𝟙 _
  | _, _, left _ _ => homOfLE inf_le_left
  | _, _, right _ _ => homOfLE inf_le_right
@[simps]
def diagram : Pairwise ι ⥤ α where
  obj := diagramObj U
  map := diagramMap U
end
section
variable [CompleteLattice α]
def coconeιApp : ∀ o : Pairwise ι, diagramObj U o ⟶ iSup U
  | single i => homOfLE (le_iSup U i)
  | pair i _ => homOfLE inf_le_left ≫ homOfLE (le_iSup U i)
@[simps]
def cocone : Cocone (diagram U) where
  pt := iSup U
  ι := { app := coconeιApp U }
def coconeIsColimit : IsColimit (cocone U) where
  desc s := homOfLE
    (by
      apply CompleteSemilatticeSup.sSup_le
      rintro _ ⟨j, rfl⟩
      exact (s.ι.app (single j)).le)
end
end Pairwise
end CategoryTheory