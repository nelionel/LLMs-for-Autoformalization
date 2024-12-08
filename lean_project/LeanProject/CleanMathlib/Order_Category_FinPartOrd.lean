import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Order.Category.PartOrd
universe u v
open CategoryTheory
structure FinPartOrd where
  toPartOrd : PartOrd
  [isFintype : Fintype toPartOrd]
namespace FinPartOrd
instance : CoeSort FinPartOrd Type* :=
  ⟨fun X => X.toPartOrd⟩
instance (X : FinPartOrd) : PartialOrder X :=
  X.toPartOrd.str
attribute [instance] FinPartOrd.isFintype
def of (α : Type*) [PartialOrder α] [Fintype α] : FinPartOrd :=
  ⟨⟨α, inferInstance⟩⟩
@[simp]
theorem coe_of (α : Type*) [PartialOrder α] [Fintype α] : ↥(of α) = α := rfl
instance : Inhabited FinPartOrd :=
  ⟨of PUnit⟩
instance largeCategory : LargeCategory FinPartOrd :=
  InducedCategory.category FinPartOrd.toPartOrd
instance concreteCategory : ConcreteCategory FinPartOrd :=
  InducedCategory.concreteCategory FinPartOrd.toPartOrd
instance hasForgetToPartOrd : HasForget₂ FinPartOrd PartOrd :=
  InducedCategory.hasForget₂ FinPartOrd.toPartOrd
instance hasForgetToFintype : HasForget₂ FinPartOrd FintypeCat where
  forget₂ :=
    { obj := fun X => ⟨X, inferInstance⟩
      map := fun {X Y} (f : OrderHom X Y) => ⇑f }
@[simps]
def Iso.mk {α β : FinPartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom _ _)
  inv := (e.symm : OrderHom _ _)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
@[simps]
def dual : FinPartOrd ⥤ FinPartOrd where
  obj X := of Xᵒᵈ
  map {_ _} := OrderHom.dual
@[simps]
def dualEquiv : FinPartOrd ≌ FinPartOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end FinPartOrd
theorem FinPartOrd_dual_comp_forget_to_partOrd :
    FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrd =
      forget₂ FinPartOrd PartOrd ⋙ PartOrd.dual := rfl