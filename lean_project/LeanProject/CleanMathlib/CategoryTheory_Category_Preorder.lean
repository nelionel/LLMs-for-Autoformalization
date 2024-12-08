import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Order.Hom.Basic
import Mathlib.Data.ULift
universe u v
namespace Preorder
open CategoryTheory
instance (priority := 100) smallCategory (α : Type u) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans _ _ _ f.down.down g.down.down⟩⟩
instance subsingleton_hom {α : Type u} [Preorder α] (U V : α) :
  Subsingleton (U ⟶ V) := ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _ )⟩
end Preorder
namespace CategoryTheory
open Opposite
variable {X : Type u} [Preorder X]
def homOfLE {x y : X} (h : x ≤ y) : x ⟶ y :=
  ULift.up (PLift.up h)
@[inherit_doc homOfLE]
abbrev _root_.LE.le.hom := @homOfLE
@[simp]
theorem homOfLE_refl {x : X} (h : x ≤ x) : h.hom = 𝟙 x :=
  rfl
@[simp]
theorem homOfLE_comp {x y z : X} (h : x ≤ y) (k : y ≤ z) :
    homOfLE h ≫ homOfLE k = homOfLE (h.trans k) :=
  rfl
theorem leOfHom {x y : X} (h : x ⟶ y) : x ≤ y :=
  h.down.down
@[nolint defLemma, inherit_doc leOfHom]
abbrev _root_.Quiver.Hom.le := @leOfHom
@[simp]
theorem homOfLE_leOfHom {x y : X} (h : x ⟶ y) : h.le.hom = h :=
  rfl
lemma homOfLE_isIso_of_eq {x y : X} (h : x ≤ y) (heq : x = y) :
    IsIso (homOfLE h) :=
  ⟨homOfLE (le_of_eq heq.symm), by simp⟩
@[simp, reassoc]
lemma homOfLE_comp_eqToHom {a b c : X} (hab : a ≤ b) (hbc : b = c) :
    homOfLE hab ≫ eqToHom hbc = homOfLE (hab.trans (le_of_eq hbc)) :=
  rfl
@[simp, reassoc]
lemma eqToHom_comp_homOfLE {a b c : X} (hab : a = b) (hbc : b ≤ c) :
    eqToHom hab ≫ homOfLE hbc = homOfLE ((le_of_eq hab).trans hbc) :=
  rfl
@[simp, reassoc]
lemma homOfLE_op_comp_eqToHom {a b c : X} (hab : b ≤ a) (hbc : op b = op c) :
    (homOfLE hab).op ≫ eqToHom hbc = (homOfLE ((le_of_eq (op_injective hbc.symm)).trans hab)).op :=
  rfl
@[simp, reassoc]
lemma eqToHom_comp_homOfLE_op {a b c : X} (hab : op a = op b) (hbc : c ≤ b) :
    eqToHom hab ≫ (homOfLE hbc).op = (homOfLE (hbc.trans (le_of_eq (op_injective hab.symm)))).op :=
  rfl
def opHomOfLE {x y : Xᵒᵖ} (h : unop x ≤ unop y) : y ⟶ x :=
  (homOfLE h).op
theorem le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y ≤ unop x :=
  h.unop.le
instance uniqueToTop [OrderTop X] {x : X} : Unique (x ⟶ ⊤) where
  default := homOfLE le_top
  uniq := fun a => by rfl
instance uniqueFromBot [OrderBot X] {x : X} : Unique (⊥ ⟶ x) where
  default := homOfLE bot_le
  uniq := fun a => by rfl
variable (X) in
@[simps]
def orderDualEquivalence : Xᵒᵈ ≌ Xᵒᵖ where
  functor :=
    { obj := fun x => op (OrderDual.ofDual x)
      map := fun f => (homOfLE (leOfHom f)).op }
  inverse :=
    { obj := fun x => OrderDual.toDual x.unop
      map := fun f => (homOfLE (leOfHom f.unop)) }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
end CategoryTheory
section
open CategoryTheory
variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
def Monotone.functor {f : X → Y} (h : Monotone f) : X ⥤ Y where
  obj := f
  map g := CategoryTheory.homOfLE (h g.le)
@[simp]
theorem Monotone.functor_obj {f : X → Y} (h : Monotone f) : h.functor.obj = f :=
  rfl
instance (f : X ↪o Y) : f.monotone.functor.Full where
  map_surjective h := ⟨homOfLE (f.map_rel_iff.1 h.le), rfl⟩
@[simps]
def OrderIso.equivalence (e : X ≃o Y) : X ≌ Y where
  functor := e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))
end
namespace CategoryTheory
section Preorder
variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]
@[mono]
theorem Functor.monotone (f : X ⥤ Y) : Monotone f.obj := fun _ _ hxy => (f.map hxy.hom).le
end Preorder
section PartialOrder
variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]
theorem Iso.to_eq {x y : X} (f : x ≅ y) : x = y :=
  le_antisymm f.hom.le f.inv.le
def Equivalence.toOrderIso (e : X ≌ Y) : X ≃o Y where
  toFun := e.functor.obj
  invFun := e.inverse.obj
  left_inv a := (e.unitIso.app a).to_eq.symm
  right_inv b := (e.counitIso.app b).to_eq
  map_rel_iff' {a a'} :=
    ⟨fun h =>
      ((Equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (Equivalence.unitInv e).app a').le,
      fun h : a ≤ a' => (e.functor.map h.hom).le⟩
@[simp]
theorem Equivalence.toOrderIso_apply (e : X ≌ Y) (x : X) : e.toOrderIso x = e.functor.obj x :=
  rfl
@[simp]
theorem Equivalence.toOrderIso_symm_apply (e : X ≌ Y) (y : Y) :
    e.toOrderIso.symm y = e.inverse.obj y :=
  rfl
end PartialOrder
end CategoryTheory