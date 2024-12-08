import Mathlib.Order.Category.Lat
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Sets.Opens
universe u
open CategoryTheory Opposite Order TopologicalSpace
def Frm :=
  Bundled Frame
namespace Frm
instance : CoeSort Frm Type* :=
  Bundled.coeSort
instance (X : Frm) : Frame X :=
  X.str
def of (α : Type*) [Frame α] : Frm :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α := rfl
instance : Inhabited Frm :=
  ⟨of PUnit⟩
abbrev Hom (α β : Type*) [Frame α] [Frame β] : Type _ :=
  FrameHom α β
instance bundledHom : BundledHom Hom where
  toFun {α β} _ _ := ((↑) : FrameHom α β → α → β)
  id {α} _ := FrameHom.id α
  comp _ _ _ := FrameHom.comp
  hom_ext _ _ := DFunLike.coe_injective
deriving instance LargeCategory, Category for Frm
instance : ConcreteCategory Frm := by
  unfold Frm
  infer_instance
instance hasForgetToLat : HasForget₂ Frm Lat where
  forget₂ :=
    { obj := fun X => ⟨X, _⟩
      map := fun {_ _} => FrameHom.toLatticeHom }
@[simps]
def Iso.mk {α β : Frm.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : FrameHom _ _)
  inv := (e.symm : FrameHom _ _)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
end Frm
@[simps]
def topCatOpToFrm : TopCatᵒᵖ ⥤ Frm where
  obj X := Frm.of (Opens (unop X : TopCat))
  map f := Opens.comap <| Quiver.Hom.unop f
  map_id _ := Opens.comap_id
instance CompHausOpToFrame.faithful : (compHausToTop.op ⋙ topCatOpToFrm.{u}).Faithful :=
  ⟨fun h => Quiver.Hom.unop_inj <| Opens.comap_injective h⟩