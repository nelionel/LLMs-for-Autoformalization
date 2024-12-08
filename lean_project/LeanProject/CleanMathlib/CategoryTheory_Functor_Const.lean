import Mathlib.CategoryTheory.Opposites
universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory
namespace CategoryTheory.Functor
variable (J : Type u₁) [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
@[simps]
def const : C ⥤ J ⥤ C where
  obj X :=
    { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map f := { app := fun _ => f }
namespace const
open Opposite
variable {J}
@[simps]
def opObjOp (X : C) : (const Jᵒᵖ).obj (op X) ≅ ((const J).obj X).op where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
def opObjUnop (X : Cᵒᵖ) : (const Jᵒᵖ).obj (unop X) ≅ ((const J).obj X).leftOp where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
@[simp]
theorem opObjUnop_hom_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).hom.app j = 𝟙 _ :=
  rfl
@[simp]
theorem opObjUnop_inv_app (X : Cᵒᵖ) (j : Jᵒᵖ) : (opObjUnop.{v₁, v₂} X).inv.app j = 𝟙 _ :=
  rfl
@[simp]
theorem unop_functor_op_obj_map (X : Cᵒᵖ) {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    (unop ((Functor.op (const J)).obj X)).map f = 𝟙 (unop X) :=
  rfl
end const
section
variable {D : Type u₃} [Category.{v₃} D]
@[simps]
def constComp (X : C) (F : C ⥤ D) : (const J).obj X ⋙ F ≅ (const J).obj (F.obj X) where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
instance [Nonempty J] : Faithful (const J : C ⥤ J ⥤ C) where
  map_injective e := NatTrans.congr_app e (Classical.arbitrary J)
@[simps!]
def compConstIso (F : C ⥤ D) :
    F ⋙ Functor.const J ≅ Functor.const J ⋙ (whiskeringRight J C D).obj F :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat))
    (by aesop_cat)
@[simps!]
def constCompWhiskeringLeftIso (F : J ⥤ D) :
    const D ⋙ (whiskeringLeft J D C).obj F ≅ const J :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => Iso.refl _
end
end CategoryTheory.Functor