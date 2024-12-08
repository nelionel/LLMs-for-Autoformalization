import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Category.Preord
import Mathlib.CategoryTheory.Adjunction.Basic
open CategoryTheory
universe u
def PartOrd :=
  Bundled PartialOrder
namespace PartOrd
instance : BundledHom.ParentProjection @PartialOrder.toPreorder :=
  ⟨⟩
deriving instance LargeCategory for PartOrd
instance : ConcreteCategory PartOrd :=
  BundledHom.concreteCategory _
instance : CoeSort PartOrd Type* :=
  Bundled.coeSort
def of (α : Type*) [PartialOrder α] : PartOrd :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [PartialOrder α] : ↥(of α) = α :=
  rfl
instance : Inhabited PartOrd :=
  ⟨of PUnit⟩
instance (α : PartOrd) : PartialOrder α :=
  α.str
instance hasForgetToPreord : HasForget₂ PartOrd Preord :=
  BundledHom.forget₂ _ _
@[simps]
def Iso.mk {α β : PartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom α β)
  inv := (e.symm : OrderHom β α)
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x
@[simps]
def dual : PartOrd ⥤ PartOrd where
  obj X := of Xᵒᵈ
  map := OrderHom.dual
@[simps functor inverse]
def dualEquiv : PartOrd ≌ PartOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end PartOrd
theorem partOrd_dual_comp_forget_to_preord :
    PartOrd.dual ⋙ forget₂ PartOrd Preord =
      forget₂ PartOrd Preord ⋙ Preord.dual :=
  rfl
def preordToPartOrd : Preord.{u} ⥤ PartOrd where
  obj X := PartOrd.of (Antisymmetrization X (· ≤ ·))
  map f := f.antisymmetrization
  map_id X := by
    ext x
    exact Quotient.inductionOn' x fun x => Quotient.map'_mk'' _ (fun a b => id) _
  map_comp f g := by
    ext x
    exact Quotient.inductionOn' x fun x => OrderHom.antisymmetrization_apply_mk _ _
def preordToPartOrdForgetAdjunction :
    preordToPartOrd.{u} ⊣ forget₂ PartOrd Preord :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f =>
            ⟨f.toFun ∘ toAntisymmetrization (· ≤ ·), f.mono.comp toAntisymmetrization_mono⟩
          invFun := fun f =>
            ⟨fun a => Quotient.liftOn' a f.toFun (fun _ _ h => (AntisymmRel.image h f.mono).eq),
              fun a b => Quotient.inductionOn₂' a b fun _ _ h => f.mono h⟩
          left_inv := fun _ =>
            OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun _ => rfl
          right_inv := fun _ => OrderHom.ext _ _ <| funext fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun _ => rfl
      homEquiv_naturality_right := fun _ _ => OrderHom.ext _ _ <| funext fun _ => rfl }
@[simps! inv_app_coe, simps! (config := .lemmasOnly) hom_app_coe]
def preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd :
    preordToPartOrd.{u} ⋙ PartOrd.dual ≅ Preord.dual ⋙ preordToPartOrd :=
  NatIso.ofComponents (fun _ => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _)
    (fun _ => OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun _ => rfl)
attribute [nolint simpNF] preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_coe