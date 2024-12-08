import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.Heyting.Hom
universe u
open CategoryTheory Opposite Order
def HeytAlg :=
  Bundled HeytingAlgebra
namespace HeytAlg
instance : CoeSort HeytAlg Type* :=
  Bundled.coeSort
instance (X : HeytAlg) : HeytingAlgebra X :=
  X.str
def of (α : Type*) [HeytingAlgebra α] : HeytAlg :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [HeytingAlgebra α] : ↥(of α) = α :=
  rfl
instance : Inhabited HeytAlg :=
  ⟨of PUnit⟩
instance bundledHom : BundledHom HeytingHom where
  toFun α β [HeytingAlgebra α] [HeytingAlgebra β] := (DFunLike.coe : HeytingHom α β → α → β)
  id := @HeytingHom.id
  comp := @HeytingHom.comp
  hom_ext α β [HeytingAlgebra α] [HeytingAlgebra β] := DFunLike.coe_injective
deriving instance LargeCategory for HeytAlg
instance : ConcreteCategory HeytAlg := by
  dsimp [HeytAlg]
  infer_instance
instance {X Y : HeytAlg.{u}} : FunLike (X ⟶ Y) ↑X ↑Y :=
  HeytingHom.instFunLike
instance {X Y : HeytAlg.{u}} : HeytingHomClass (X ⟶ Y) ↑X ↑Y :=
  HeytingHom.instHeytingHomClass
@[simps]
instance hasForgetToLat : HasForget₂ HeytAlg BddDistLat where
  forget₂ :=
    { obj := fun X => BddDistLat.of X
      map := fun {X Y} f => (f : BoundedLatticeHom X Y) }
@[simps]
def Iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : HeytingHom _ _)
  inv := (e.symm : HeytingHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
end HeytAlg