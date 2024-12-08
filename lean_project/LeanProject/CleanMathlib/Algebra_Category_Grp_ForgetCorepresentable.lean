import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Yoneda
universe u
open CategoryTheory Opposite
namespace MonoidHom
@[simps]
def precompEquiv {α β : Type*} [Monoid α] [Monoid β] (e : α ≃* β) (γ : Type*) [Monoid γ] :
    (β →* γ) ≃ (α →* γ) where
  toFun f := f.comp e
  invFun g := g.comp e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
@[simps]
def fromMultiplicativeIntEquiv (α : Type u) [Group α] : (Multiplicative ℤ →* α) ≃ α where
  toFun φ := φ (Multiplicative.ofAdd 1)
  invFun x := zpowersHom α x
  left_inv φ := by ext; simp
  right_inv x := by simp
@[simps!]
def fromULiftMultiplicativeIntEquiv (α : Type u) [Group α] :
    (ULift.{u} (Multiplicative ℤ) →* α) ≃ α :=
  (precompEquiv (MulEquiv.ulift.symm) _).trans (fromMultiplicativeIntEquiv α)
end MonoidHom
namespace AddMonoidHom
@[simps]
def precompEquiv {α β : Type*} [AddMonoid α] [AddMonoid β] (e : α ≃+ β) (γ : Type*) [AddMonoid γ] :
    (β →+ γ) ≃ (α →+ γ) where
  toFun f := f.comp e
  invFun g := g.comp e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
@[simps]
def fromIntEquiv (α : Type u) [AddGroup α] : (ℤ →+ α) ≃ α where
  toFun φ := φ 1
  invFun x := zmultiplesHom α x
  left_inv φ := by ext; simp
  right_inv x := by simp
@[simps!]
def fromULiftIntEquiv (α : Type u) [AddGroup α] : (ULift.{u} ℤ →+ α) ≃ α :=
  (precompEquiv (AddEquiv.ulift.symm) _).trans (fromIntEquiv α)
end AddMonoidHom
def Grp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget Grp.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeIntEquiv M.α).toIso))
def CommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget CommGrp.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeIntEquiv M.α).toIso))
def AddGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddGrp.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftIntEquiv M.α).toIso))
def AddCommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddCommGrp.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftIntEquiv M.α).toIso))
instance Grp.forget_isCorepresentable :
    (forget Grp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' Grp.coyonedaObjIsoForget
instance CommGrp.forget_isCorepresentable :
    (forget CommGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommGrp.coyonedaObjIsoForget
instance AddGrp.forget_isCorepresentable :
    (forget AddGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddGrp.coyonedaObjIsoForget
instance AddCommGrp.forget_isCorepresentable :
    (forget AddCommGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommGrp.coyonedaObjIsoForget