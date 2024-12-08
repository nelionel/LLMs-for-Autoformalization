import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Induced
import Mathlib.CategoryTheory.Quotient
universe v v' u u' w
open CategoryTheory Category
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (r : HomRel C) (A : Type w) [AddMonoid A] [HasShift C A] [HasShift D A]
namespace HomRel
class IsCompatibleWithShift : Prop where
  condition : ∀ (a : A) ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → r (f⟦a⟧') (g⟦a⟧')
end HomRel
namespace CategoryTheory
noncomputable instance HasShift.quotient [r.IsCompatibleWithShift A] :
    HasShift (Quotient r) A :=
  HasShift.induced (Quotient.functor r) A
    (fun a => Quotient.lift r (shiftFunctor C a ⋙ Quotient.functor r)
      (fun _ _ _ _ hfg => Quotient.sound r (HomRel.IsCompatibleWithShift.condition _ _ _ hfg)))
    (fun _ => Quotient.lift.isLift _ _ _)
noncomputable instance Quotient.functor_commShift [r.IsCompatibleWithShift A] :
    (Quotient.functor r).CommShift A :=
  Functor.CommShift.ofInduced _ _ _ _
attribute [irreducible] HasShift.quotient Quotient.functor_commShift
namespace Quotient
variable [r.IsCompatibleWithShift A] [F.CommShift A]
    (hF : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)
namespace LiftCommShift
variable {A}
noncomputable def iso (a : A) :
    shiftFunctor (Quotient r) a ⋙ lift r F hF ≅ lift r F hF ⋙ shiftFunctor D a :=
  natIsoLift r ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((functor r).commShiftIso a).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (lift.isLift r F hF) ≪≫ F.commShiftIso a ≪≫
    isoWhiskerRight (lift.isLift r F hF).symm _ ≪≫ Functor.associator _ _ _)
@[simp]
lemma iso_hom_app (a : A) (X : C) :
    (iso F r hF a).hom.app ((functor r).obj X) =
      (lift r F hF).map (((functor r).commShiftIso a).inv.app X) ≫
      (F.commShiftIso a).hom.app X := by
  dsimp only [iso, natIsoLift]
  rw [natTransLift_app]
  dsimp
  erw [comp_id, id_comp, id_comp, id_comp, Functor.map_id, comp_id]
@[simp]
lemma iso_inv_app (a : A) (X : C) :
    (iso F r hF a).inv.app ((functor r).obj X) =
      (F.commShiftIso a).inv.app X ≫
      (lift r F hF).map (((functor r).commShiftIso a).hom.app X) := by
  dsimp only [iso, natIsoLift]
  rw [natTransLift_app]
  dsimp
  erw [id_comp, comp_id, comp_id, comp_id, Functor.map_id, id_comp]
attribute [irreducible] iso
end LiftCommShift
noncomputable instance liftCommShift :
    (Quotient.lift r F hF).CommShift A where
  iso := LiftCommShift.iso F r hF
  zero := by
    ext1
    apply natTrans_ext
    ext X
    dsimp
    rw [LiftCommShift.iso_hom_app, (functor r).commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.CommShift.isoZero_inv_app,
      Functor.map_comp, assoc, F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      lift_map_functor_map, ← F.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp [lift_obj_functor_obj]
    rw [F.map_id, id_comp]
  add a b := by
    ext1
    apply natTrans_ext
    ext X
    dsimp
    rw [LiftCommShift.iso_hom_app, (functor r).commShiftIso_add, F.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_hom_app,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, assoc, assoc, assoc, LiftCommShift.iso_hom_app, lift_map_functor_map]
    congr 1
    rw [← cancel_epi ((shiftFunctor (Quotient r) b ⋙ lift r F hF).map
      (NatTrans.app (Functor.commShiftIso (functor r) a).hom X))]
    erw [(LiftCommShift.iso F r hF b).hom.naturality_assoc
      (((functor r).commShiftIso a).hom.app X), LiftCommShift.iso_hom_app,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    dsimp
    simp only [Functor.comp_obj, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Functor.map_id, id_comp, Iso.hom_inv_id_app, lift_obj_functor_obj]
instance liftCommShift_compatibility :
    NatTrans.CommShift (Quotient.lift.isLift r F hF).hom A where
  comm' a := by
    ext X
    dsimp
    erw [Functor.map_id, id_comp, comp_id]
    rw [Functor.commShiftIso_comp_hom_app]
    erw [LiftCommShift.iso_hom_app]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, id_comp]
end Quotient
end CategoryTheory