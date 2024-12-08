import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Order.Category.BoolAlg
universe u
open CategoryTheory Order
def BoolRing :=
  Bundled BooleanRing
namespace BoolRing
instance : CoeSort BoolRing Type* :=
  Bundled.coeSort
instance (X : BoolRing) : BooleanRing X :=
  X.str
def of (α : Type*) [BooleanRing α] : BoolRing :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α :=
  rfl
instance : Inhabited BoolRing :=
  ⟨of PUnit⟩
instance : BundledHom.ParentProjection @BooleanRing.toCommRing :=
  ⟨⟩
deriving instance LargeCategory for BoolRing
instance : ConcreteCategory BoolRing := by
  dsimp [BoolRing]
  infer_instance
instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat :=
  BundledHom.forget₂ _ _
@[simps]
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β where
  hom := (e : RingHom _ _)
  inv := (e.symm : RingHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
end BoolRing
@[simps]
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg where
  forget₂ :=
    { obj := fun X => BoolAlg.of (AsBoolAlg X)
      map := fun {_ _} => RingHom.asBoolAlg }
instance {X : BoolAlg} :
    BooleanAlgebra ↑(BddDistLat.toBddLat (X.toBddDistLat)).toLat :=
  BoolAlg.instBooleanAlgebra _
@[simps]
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing where
  forget₂ :=
    { obj := fun X => BoolRing.of (AsBoolRing X)
      map := fun {_ _} => BoundedLatticeHom.asBoolRing }
@[simps functor inverse]
def boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg where
  functor := forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {_ _} _ => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {_ _} _ => rfl