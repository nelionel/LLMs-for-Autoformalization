import Mathlib.Order.Category.Lat
universe u
open CategoryTheory
def DistLat :=
  Bundled DistribLattice
namespace DistLat
instance : CoeSort DistLat Type* :=
  Bundled.coeSort
instance (X : DistLat) : DistribLattice X :=
  X.str
def of (α : Type*) [DistribLattice α] : DistLat :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [DistribLattice α] : ↥(of α) = α :=
  rfl
instance : Inhabited DistLat :=
  ⟨of PUnit⟩
instance : BundledHom.ParentProjection @DistribLattice.toLattice :=
  ⟨⟩
deriving instance LargeCategory for DistLat
instance : ConcreteCategory DistLat :=
  BundledHom.concreteCategory _
instance hasForgetToLat : HasForget₂ DistLat Lat :=
  BundledHom.forget₂ _ _
@[simps]
def Iso.mk {α β : DistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : LatticeHom α β)
  inv := (e.symm : LatticeHom β α)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
@[simps]
def dual : DistLat ⥤ DistLat where
  obj X := of Xᵒᵈ
  map := LatticeHom.dual
@[simps functor inverse]
def dualEquiv : DistLat ≌ DistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl
end DistLat
theorem distLat_dual_comp_forget_to_Lat :
    DistLat.dual ⋙ forget₂ DistLat Lat = forget₂ DistLat Lat ⋙ Lat.dual :=
  rfl