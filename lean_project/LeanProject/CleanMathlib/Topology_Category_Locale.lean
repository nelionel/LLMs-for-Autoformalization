import Mathlib.Order.Category.Frm
universe u
open CategoryTheory Opposite Order TopologicalSpace
def Locale :=
  Frmᵒᵖ deriving LargeCategory
namespace Locale
instance : CoeSort Locale Type* :=
  ⟨fun X => X.unop⟩
instance (X : Locale) : Frame X :=
  X.unop.str
def of (α : Type*) [Frame α] : Locale :=
  op <| Frm.of α
@[simp]
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α :=
  rfl
instance : Inhabited Locale :=
  ⟨of PUnit⟩
end Locale
@[simps!]
def topToLocale : TopCat ⥤ Locale :=
  topCatOpToFrm.rightOp
instance CompHausToLocale.faithful : (compHausToTop ⋙ topToLocale.{u}).Faithful :=
  ⟨fun h => by
    dsimp at h
    exact Opens.comap_injective (Quiver.Hom.op_inj h)⟩