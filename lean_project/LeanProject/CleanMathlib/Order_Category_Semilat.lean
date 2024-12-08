import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Lattice
universe u
open CategoryTheory
structure SemilatSupCat : Type (u + 1) where
  protected X : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot.{u} X]
structure SemilatInfCat : Type (u + 1) where
  protected X : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop.{u} X]
namespace SemilatSupCat
instance : CoeSort SemilatSupCat Type* :=
  ⟨SemilatSupCat.X⟩
attribute [instance] isSemilatticeSup isOrderBot
def of (α : Type*) [SemilatticeSup α] [OrderBot α] : SemilatSupCat :=
  ⟨α⟩
@[simp]
theorem coe_of (α : Type*) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl
instance : Inhabited SemilatSupCat :=
  ⟨of PUnit⟩
instance : LargeCategory.{u} SemilatSupCat where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp f g := g.comp f
  id_comp := SupBotHom.comp_id
  comp_id := SupBotHom.id_comp
  assoc _ _ _ := SupBotHom.comp_assoc _ _ _
instance instFunLike (X Y : SemilatSupCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (SupBotHom X Y) X Y from inferInstance
instance : ConcreteCategory SemilatSupCat where
  forget :=
    { obj := SemilatSupCat.X
      map := DFunLike.coe }
  forget_faithful := ⟨(DFunLike.coe_injective ·)⟩
instance hasForgetToPartOrd : HasForget₂ SemilatSupCat PartOrd where
  forget₂ :=
    { obj := fun X => {α := X}
      map := fun f => ⟨f.toSupHom, OrderHomClass.mono f.toSupHom⟩ }
@[simp]
theorem coe_forget_to_partOrd (X : SemilatSupCat) :
    ↥((forget₂ SemilatSupCat PartOrd).obj X) = ↥X :=
  rfl
end SemilatSupCat
namespace SemilatInfCat
instance : CoeSort SemilatInfCat Type* :=
  ⟨SemilatInfCat.X⟩
attribute [instance] isSemilatticeInf isOrderTop
def of (α : Type*) [SemilatticeInf α] [OrderTop α] : SemilatInfCat :=
  ⟨α⟩
@[simp]
theorem coe_of (α : Type*) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl
instance : Inhabited SemilatInfCat :=
  ⟨of PUnit⟩
instance : LargeCategory.{u} SemilatInfCat where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp f g := g.comp f
  id_comp := InfTopHom.comp_id
  comp_id := InfTopHom.id_comp
  assoc _ _ _ := InfTopHom.comp_assoc _ _ _
instance instFunLike (X Y : SemilatInfCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (InfTopHom X Y) X Y from inferInstance
instance : ConcreteCategory SemilatInfCat where
  forget :=
    { obj := SemilatInfCat.X
      map := DFunLike.coe }
  forget_faithful := ⟨(DFunLike.coe_injective ·)⟩
instance hasForgetToPartOrd : HasForget₂ SemilatInfCat PartOrd where
  forget₂ :=
    { obj := fun X => ⟨X, inferInstance⟩
      map := fun f => ⟨f.toInfHom, OrderHomClass.mono f.toInfHom⟩ }
@[simp]
theorem coe_forget_to_partOrd (X : SemilatInfCat) :
    ↥((forget₂ SemilatInfCat PartOrd).obj X) = ↥X :=
  rfl
end SemilatInfCat
namespace SemilatSupCat
@[simps]
def Iso.mk {α β : SemilatSupCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : SupBotHom _ _)
  inv := (e.symm : SupBotHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
@[simps]
def dual : SemilatSupCat ⥤ SemilatInfCat where
  obj X := SemilatInfCat.of Xᵒᵈ
  map {_ _} := SupBotHom.dual
end SemilatSupCat
namespace SemilatInfCat
@[simps]
def Iso.mk {α β : SemilatInfCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : InfTopHom _ _)
  inv := (e.symm :  InfTopHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
@[simps]
def dual : SemilatInfCat ⥤ SemilatSupCat where
  obj X := SemilatSupCat.of Xᵒᵈ
  map {_ _} := InfTopHom.dual
end SemilatInfCat
@[simps functor inverse]
def SemilatSupCatEquivSemilatInfCat : SemilatSupCat ≌ SemilatInfCat where
  functor := SemilatSupCat.dual
  inverse := SemilatInfCat.dual
  unitIso := NatIso.ofComponents fun X => SemilatSupCat.Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => SemilatInfCat.Iso.mk <| OrderIso.dualDual X
theorem SemilatSupCat_dual_comp_forget_to_partOrd :
    SemilatSupCat.dual ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ SemilatSupCat PartOrd ⋙ PartOrd.dual :=
  rfl
theorem SemilatInfCat_dual_comp_forget_to_partOrd :
    SemilatInfCat.dual ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ SemilatInfCat PartOrd ⋙ PartOrd.dual :=
  rfl