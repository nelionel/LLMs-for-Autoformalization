import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Category.BoolAlg
import Mathlib.Order.Category.FinBddDistLat
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Set.Subsingleton
universe u
open CategoryTheory OrderDual Opposite
structure FinBoolAlg where
  toBoolAlg : BoolAlg
  [isFintype : Fintype toBoolAlg]
namespace FinBoolAlg
instance : CoeSort FinBoolAlg Type* :=
  ⟨fun X => X.toBoolAlg⟩
instance (X : FinBoolAlg) : BooleanAlgebra X :=
  X.toBoolAlg.str
attribute [instance] FinBoolAlg.isFintype
def of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg :=
  ⟨{α := α}⟩
@[simp]
theorem coe_of (α : Type*) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl
instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩
instance largeCategory : LargeCategory FinBoolAlg :=
  InducedCategory.category FinBoolAlg.toBoolAlg
instance concreteCategory : ConcreteCategory FinBoolAlg :=
  InducedCategory.concreteCategory FinBoolAlg.toBoolAlg
instance instFunLike {X Y : FinBoolAlg} : FunLike (X ⟶ Y) X Y :=
  BoundedLatticeHom.instFunLike
instance instBoundedLatticeHomClass {X Y : FinBoolAlg} : BoundedLatticeHomClass (X ⟶ Y) X Y :=
  BoundedLatticeHom.instBoundedLatticeHomClass
instance hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg :=
  InducedCategory.hasForget₂ FinBoolAlg.toBoolAlg
instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat where
  forget₂.obj X := FinBddDistLat.of X
  forget₂.map f := f
  forget_comp := rfl
instance forgetToBoolAlg_full : (forget₂ FinBoolAlg BoolAlg).Full :=
  InducedCategory.full _
instance forgetToBoolAlgFaithful : (forget₂ FinBoolAlg BoolAlg).Faithful :=
  InducedCategory.faithful _
@[simps]
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd where
  forget₂.obj X := FinPartOrd.of X
  forget₂.map {X Y} f := show OrderHom X Y from ↑(show BoundedLatticeHom X Y from f)
instance forgetToFinPartOrdFaithful : (forget₂ FinBoolAlg FinPartOrd).Faithful :=
  ⟨fun {X Y} f g h => by
    dsimp at *
    apply DFunLike.coe_injective
    dsimp
    ext x
    apply_fun (fun f => f x) at h
    exact h ⟩
@[simps]
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
@[simps]
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj X := of Xᵒᵈ
  map {_ _} := BoundedLatticeHom.dual
@[simps functor inverse]
def dualEquiv : FinBoolAlg ≌ FinBoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
end FinBoolAlg
theorem finBoolAlg_dual_comp_forget_to_finBddDistLat :
    FinBoolAlg.dual ⋙ forget₂ FinBoolAlg FinBddDistLat =
      forget₂ FinBoolAlg FinBddDistLat ⋙ FinBddDistLat.dual :=
  rfl
@[simps]
def fintypeToFinBoolAlgOp : FintypeCat ⥤ FinBoolAlgᵒᵖ where
  obj X := op <| FinBoolAlg.of (Set X)
  map {X Y} f :=
    Quiver.Hom.op <| (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))