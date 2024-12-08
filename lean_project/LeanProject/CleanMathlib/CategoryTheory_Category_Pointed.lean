import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
open CategoryTheory
universe u
structure Pointed : Type (u + 1) where
  protected X : Type u
  point : X
namespace Pointed
instance : CoeSort Pointed Type* :=
  ⟨Pointed.X⟩
def of {X : Type*} (point : X) : Pointed :=
  ⟨X, point⟩
@[simp]
theorem coe_of {X : Type*} (point : X) : ↥(of point) = X :=
  rfl
alias _root_.Prod.Pointed := of
instance : Inhabited Pointed :=
  ⟨of ((), ())⟩
@[ext]
protected structure Hom (X Y : Pointed.{u}) : Type u where
  toFun : X → Y
  map_point : toFun X.point = Y.point
namespace Hom
@[simps]
def id (X : Pointed) : Pointed.Hom X X :=
  ⟨_root_.id, rfl⟩
instance (X : Pointed) : Inhabited (Pointed.Hom X X) :=
  ⟨id X⟩
@[simps]
def comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : Pointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩
end Hom
instance largeCategory : LargeCategory Pointed where
  Hom := Pointed.Hom
  id := Hom.id
  comp := @Hom.comp
@[simp] lemma Hom.id_toFun' (X : Pointed.{u}) : (𝟙 X : X ⟶ X).toFun = _root_.id := rfl
@[simp] lemma Hom.comp_toFun' {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl
instance concreteCategory : ConcreteCategory Pointed where
  forget :=
    { obj := Pointed.X
      map := @Hom.toFun }
  forget_faithful := ⟨@Hom.ext⟩
@[simps]
def Iso.mk {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point) : α ≅ β where
  hom := ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id := Pointed.Hom.ext e.symm_comp_self
  inv_hom_id := Pointed.Hom.ext e.self_comp_symm
end Pointed
@[simps]
def typeToPointed : Type u ⥤ Pointed.{u} where
  obj X := ⟨Option X, none⟩
  map f := ⟨Option.map f, rfl⟩
  map_id _ := Pointed.Hom.ext Option.map_id
  map_comp _ _ := Pointed.Hom.ext (Option.map_comp_map _ _).symm
def typeToPointedForgetAdjunction : typeToPointed ⊣ forget Pointed :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => f.toFun ∘ Option.some
          invFun := fun f => ⟨fun o => o.elim Y.point f, rfl⟩
          left_inv := fun f => by
            apply Pointed.Hom.ext
            funext x
            cases x
            · exact f.map_point.symm
            · rfl
          right_inv := fun _ => funext fun _ => rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Pointed.Hom.ext
        funext x
        cases x <;> rfl }