import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Order.Hom.Basic
import Mathlib.Order.CompleteBooleanAlgebra
universe u
open CategoryTheory
def Preord :=
  Bundled Preorder
namespace Preord
instance : BundledHom @OrderHom where
  toFun := @OrderHom.toFun
  id := @OrderHom.id
  comp := @OrderHom.comp
  hom_ext := @OrderHom.ext
deriving instance LargeCategory for Preord
instance : ConcreteCategory Preord :=
  BundledHom.concreteCategory _
instance : CoeSort Preord Type* :=
  Bundled.coeSort
def of (α : Type*) [Preorder α] : Preord :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [Preorder α] : ↥(of α) = α :=
  rfl
instance : Inhabited Preord :=
  ⟨of PUnit⟩
instance (α : Preord) : Preorder α :=
  α.str
@[simps]
def Iso.mk {α β : Preord.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom α β)
  inv := (e.symm : OrderHom β α)
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x
@[simps]
def dual : Preord ⥤ Preord where
  obj X := of Xᵒᵈ
  map := OrderHom.dual
@[simps functor inverse]
def dualEquiv : Preord ≌ Preord where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end Preord
@[simps]
def preordToCat : Preord.{u} ⥤ Cat where
  obj X := Cat.of X.1
  map f := f.monotone.functor
instance : preordToCat.{u}.Faithful where
  map_injective h := by ext x; exact Functor.congr_obj h x
instance : preordToCat.{u}.Full where
  map_surjective {X Y} f := ⟨⟨f.obj, @CategoryTheory.Functor.monotone X Y _ _ f⟩, rfl⟩