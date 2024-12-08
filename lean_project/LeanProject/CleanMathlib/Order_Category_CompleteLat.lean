import Mathlib.Order.Category.BddLat
import Mathlib.Order.Hom.CompleteLattice
universe u
open CategoryTheory
def CompleteLat :=
  Bundled CompleteLattice
namespace CompleteLat
instance : CoeSort CompleteLat Type* :=
  Bundled.coeSort
instance (X : CompleteLat) : CompleteLattice X :=
  X.str
def of (α : Type*) [CompleteLattice α] : CompleteLat :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [CompleteLattice α] : ↥(of α) = α :=
  rfl
instance : Inhabited CompleteLat :=
  ⟨of PUnit⟩
instance : BundledHom @CompleteLatticeHom where
  toFun _ _ f := f.toFun
  id := @CompleteLatticeHom.id
  comp := @CompleteLatticeHom.comp
  hom_ext _ _ _ _ h := DFunLike.coe_injective h
deriving instance LargeCategory for CompleteLat
instance : ConcreteCategory CompleteLat := by
  dsimp [CompleteLat]; infer_instance
instance hasForgetToBddLat : HasForget₂ CompleteLat BddLat where
  forget₂ :=
    { obj := fun X => BddLat.of X
      map := fun {_ _} => CompleteLatticeHom.toBoundedLatticeHom }
  forget_comp := rfl
@[simps]
def Iso.mk {α β : CompleteLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : CompleteLatticeHom _ _) 
  inv := (e.symm : CompleteLatticeHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
@[simps]
def dual : CompleteLat ⥤ CompleteLat where
  obj X := of Xᵒᵈ
  map {_ _} := CompleteLatticeHom.dual
@[simps functor inverse]
def dualEquiv : CompleteLat ≌ CompleteLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end CompleteLat
theorem completeLat_dual_comp_forget_to_bddLat :
    CompleteLat.dual ⋙ forget₂ CompleteLat BddLat =
    forget₂ CompleteLat BddLat ⋙ BddLat.dual :=
  rfl