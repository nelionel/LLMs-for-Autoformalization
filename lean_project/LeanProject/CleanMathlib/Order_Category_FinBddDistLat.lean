import Mathlib.Data.Fintype.Order
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.Category.FinPartOrd
universe u
open CategoryTheory
structure FinBddDistLat where
  toBddDistLat : BddDistLat
  [isFintype : Fintype toBddDistLat]
namespace FinBddDistLat
instance : CoeSort FinBddDistLat Type* :=
  ⟨fun X => X.toBddDistLat⟩
instance (X : FinBddDistLat) : DistribLattice X :=
  X.toBddDistLat.toDistLat.str
instance (X : FinBddDistLat) : BoundedOrder X :=
  X.toBddDistLat.isBoundedOrder
attribute [instance] FinBddDistLat.isFintype
def of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat :=
  ⟨⟨{α := α}⟩⟩
def of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat :=
  haveI := Fintype.toBoundedOrder α
  ⟨⟨{α := α}⟩⟩
instance : Inhabited FinBddDistLat :=
  ⟨of PUnit⟩
instance largeCategory : LargeCategory FinBddDistLat :=
  InducedCategory.category toBddDistLat
instance concreteCategory : ConcreteCategory FinBddDistLat :=
  InducedCategory.concreteCategory toBddDistLat
instance hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat :=
  InducedCategory.hasForget₂ FinBddDistLat.toBddDistLat
instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd where
  forget₂.obj X := FinPartOrd.of X
  forget₂.map {X Y} f := (show BoundedLatticeHom X Y from f : X →o Y)
@[simps]
def Iso.mk {α β : FinBddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
example {X Y : FinBddDistLat} : (X ⟶ Y) = BoundedLatticeHom X Y :=
  rfl
@[simps]
def dual : FinBddDistLat ⥤ FinBddDistLat where
  obj X := of Xᵒᵈ
  map {_ _} := BoundedLatticeHom.dual
@[simps functor inverse]
def dualEquiv : FinBddDistLat ≌ FinBddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end FinBddDistLat
theorem finBddDistLat_dual_comp_forget_to_bddDistLat :
    FinBddDistLat.dual ⋙ forget₂ FinBddDistLat BddDistLat =
      forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual :=
  rfl