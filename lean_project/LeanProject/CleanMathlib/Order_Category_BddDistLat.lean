import Mathlib.Order.Category.BddLat
import Mathlib.Order.Category.DistLat
universe u
open CategoryTheory
structure BddDistLat where
  toDistLat : DistLat
  [isBoundedOrder : BoundedOrder toDistLat]
namespace BddDistLat
instance : CoeSort BddDistLat Type* :=
  ⟨fun X => X.toDistLat⟩
instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str
attribute [instance] BddDistLat.isBoundedOrder
def of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat :=
  ⟨{α := α}⟩
@[simp]
theorem coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
instance : Inhabited BddDistLat :=
  ⟨of PUnit⟩
def toBddLat (X : BddDistLat) : BddLat :=
  BddLat.of X
@[simp]
theorem coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X :=
  rfl
instance : LargeCategory.{u} BddDistLat :=
  InducedCategory.category toBddLat
instance : ConcreteCategory BddDistLat :=
  InducedCategory.concreteCategory toBddLat
instance hasForgetToDistLat : HasForget₂ BddDistLat DistLat where
  forget₂ :=
    { obj := fun X => { α := X }
      map := fun {_ _} => BoundedLatticeHom.toLatticeHom }
instance hasForgetToBddLat : HasForget₂ BddDistLat BddLat :=
  InducedCategory.hasForget₂ toBddLat
theorem forget_bddLat_lat_eq_forget_distLat_lat :
    forget₂ BddDistLat BddLat ⋙ forget₂ BddLat Lat =
      forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat :=
  rfl
@[simps]
def Iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
@[simps]
def dual : BddDistLat ⥤ BddDistLat where
  obj X := of Xᵒᵈ
  map {_ _} := BoundedLatticeHom.dual
@[simps functor inverse]
def dualEquiv : BddDistLat ≌ BddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end BddDistLat
theorem bddDistLat_dual_comp_forget_to_distLat :
    BddDistLat.dual ⋙ forget₂ BddDistLat DistLat =
      forget₂ BddDistLat DistLat ⋙ DistLat.dual :=
  rfl