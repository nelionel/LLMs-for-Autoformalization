import Mathlib.Order.Category.HeytAlg
import Mathlib.Order.Hom.CompleteLattice
open OrderDual Opposite Set
universe u
open CategoryTheory
def BoolAlg :=
  Bundled BooleanAlgebra
namespace BoolAlg
instance : CoeSort BoolAlg Type* :=
  Bundled.coeSort
instance instBooleanAlgebra (X : BoolAlg) : BooleanAlgebra X :=
  X.str
def of (α : Type*) [BooleanAlgebra α] : BoolAlg :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl
instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩
def toBddDistLat (X : BoolAlg) : BddDistLat :=
  BddDistLat.of X
@[simp]
theorem coe_toBddDistLat (X : BoolAlg) : ↥X.toBddDistLat = ↥X :=
  rfl
instance : LargeCategory.{u} BoolAlg :=
  InducedCategory.category toBddDistLat
instance : ConcreteCategory BoolAlg :=
  InducedCategory.concreteCategory toBddDistLat
instance hasForgetToBddDistLat : HasForget₂ BoolAlg BddDistLat :=
  InducedCategory.hasForget₂ toBddDistLat
section
attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass
@[simps]
instance hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg where
  forget₂ :=
    { obj := fun X => {α := X}
      map := fun {X Y} (f : BoundedLatticeHom X Y) => show HeytingHom X Y from f }
end
@[simps]
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
@[simps]
def dual : BoolAlg ⥤ BoolAlg where
  obj X := of Xᵒᵈ
  map {_ _} := BoundedLatticeHom.dual
@[simps functor inverse]
def dualEquiv : BoolAlg ≌ BoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end BoolAlg
theorem boolAlg_dual_comp_forget_to_bddDistLat :
    BoolAlg.dual ⋙ forget₂ BoolAlg BddDistLat =
    forget₂ BoolAlg BddDistLat ⋙ BddDistLat.dual :=
  rfl
@[simps]
def typeToBoolAlgOp : Type u ⥤ BoolAlgᵒᵖ where
  obj X := op <| BoolAlg.of (Set X)
  map {X Y} f := Quiver.Hom.op
    (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))