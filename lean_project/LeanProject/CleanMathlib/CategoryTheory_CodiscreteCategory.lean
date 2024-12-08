import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.ULift
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
namespace CategoryTheory
universe u v w
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
structure Codiscrete (α : Type u) where
  as : α
@[simp]
theorem Codiscrete.mk_as {α : Type u} (X : Codiscrete α) : Codiscrete.mk X.as = X := rfl
@[simps]
def codiscreteEquiv {α : Type u} : Codiscrete α ≃ α where
  toFun := Codiscrete.as
  invFun := Codiscrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat
instance {α : Type u} [DecidableEq α] : DecidableEq (Codiscrete α) :=
  codiscreteEquiv.decidableEq
namespace Codiscrete
instance (A : Type*) : Category (Codiscrete A) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩
section
variable {C : Type u} [Category.{v} C] {A : Type w}
def functor (F : C → A) : C ⥤ Codiscrete A where
  obj := Codiscrete.mk ∘ F
  map _ := ⟨⟩
def invFunctor (F : C ⥤ Codiscrete A) : C → A := Codiscrete.as ∘ F.obj
def natTrans {F G : C ⥤ Codiscrete A} : F ⟶ G where
  app _ := ⟨⟩
def natIso {F G : C ⥤ Codiscrete A} : F ≅ G where
  hom := natTrans
  inv := natTrans
@[simps!]
def natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ functor (Codiscrete.as ∘ F.obj) := Iso.refl _
end
def functorOfFun {A B : Type*} (f : A → B) : Codiscrete A ⥤ Codiscrete B :=
  functor (f ∘ Codiscrete.as)
open Opposite
def oppositeEquivalence (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A where
  functor := functor (fun x ↦ Codiscrete.as x.unop)
  inverse := (functor (fun x ↦ Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso
def functorToCat : Type u ⥤ Cat.{0,u} where
  obj A := Cat.of (Codiscrete A)
  map := functorOfFun
open Adjunction Cat
def equivFunctorToCodiscrete {C : Type u} [Category.{v} C] {A : Type w} :
    (C → A) ≃ (C ⥤ Codiscrete A) where
  toFun := functor
  invFun := invFunctor
  left_inv _ := rfl
  right_inv _ := rfl
def adj : objects ⊣ functorToCat := mkOfHomEquiv {
  homEquiv := fun _ _ => equivFunctorToCodiscrete
  homEquiv_naturality_left_symm := fun _ _ => rfl
  homEquiv_naturality_right := fun _ _ => rfl }
def unitApp (C : Type u) [Category.{v} C] : C ⥤ Codiscrete C := functor id
def counitApp (A : Type u) : Codiscrete A → A := Codiscrete.as
lemma adj_unit_app (X : Cat.{0, u}) :
    adj.unit.app X = unitApp X := rfl
lemma adj_counit_app (A : Type u) :
    adj.counit.app A = counitApp A := rfl
lemma left_triangle_components (C : Type u) [Category.{v} C] :
    (counitApp C).comp (unitApp C).obj = id :=
  rfl
lemma right_triangle_components (X : Type u) :
    unitApp (Codiscrete X) ⋙ functorOfFun (counitApp X) = 𝟭 (Codiscrete X) :=
  rfl
end Codiscrete
end CategoryTheory