import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Lattice
universe u
open CategoryTheory
def Lat :=
  Bundled Lattice
namespace Lat
instance : CoeSort Lat Type* :=
  Bundled.coeSort
instance (X : Lat) : Lattice X :=
  X.str
def of (α : Type*) [Lattice α] : Lat :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [Lattice α] : ↥(of α) = α :=
  rfl
instance : Inhabited Lat :=
  ⟨of Bool⟩
instance : BundledHom @LatticeHom where
  toFun _ _ f := f.toFun
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext _ _ _ _ h := DFunLike.coe_injective h
instance : LargeCategory.{u} Lat :=
  BundledHom.category LatticeHom
instance : ConcreteCategory Lat :=
  BundledHom.concreteCategory LatticeHom
instance hasForgetToPartOrd : HasForget₂ Lat PartOrd where
  forget₂ :=
    { obj := fun X => Bundled.mk X inferInstance
      map := fun {X Y} (f : LatticeHom X Y) => (f : OrderHom X Y) }
@[simps]
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : LatticeHom _ _)
  inv := (e.symm : LatticeHom _ _)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
@[simps]
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map := LatticeHom.dual
@[simps functor inverse]
def dualEquiv : Lat ≌ Lat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end Lat
theorem Lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl