import Mathlib.CategoryTheory.Equivalence
namespace CategoryTheory
open Category
variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category C₅] [Category C₆]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
@[ext]
class CatCommSq where
  iso' : T ⋙ R ≅ L ⋙ B
namespace CatCommSq
def iso [h : CatCommSq T L R B] : T ⋙ R ≅ L ⋙ B := h.iso'
@[simps! iso'_hom_app iso'_inv_app]
def hComp (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
    (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆) [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂] :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  iso' := Functor.associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    Functor.associator _ _ _
@[simps! iso'_hom_app iso'_inv_app]
def vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃] :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  iso' := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (Functor.associator _ _ _).symm
section
variable (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)
@[simps! iso'_hom_app iso'_inv_app]
def hInv (_ : CatCommSq T.functor L R B.functor) : CatCommSq T.inverse R L B.inverse where
  iso' := isoWhiskerLeft _ (L.rightUnitor.symm ≪≫ isoWhiskerLeft L B.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (iso T.functor L R B.functor).symm B.inverse ≪≫
      Functor.associator _ _ _  ) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight T.counitIso _ ≪≫ Functor.leftUnitor _
lemma hInv_hInv (h : CatCommSq T.functor L R B.functor) :
    hInv T.symm R L B.symm (hInv T L R B h) = h := by
  ext X
  erw [← cancel_mono (B.functor.map (L.map (T.unitIso.hom.app X))),
    ← h.iso'.hom.naturality (T.unitIso.hom.app X), hInv_iso'_hom_app, hInv_iso'_inv_app]
  dsimp
  simp only [Functor.comp_obj, assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Equivalence.counitInv_app_functor, Functor.map_id]
  simp only [Functor.map_comp, Equivalence.fun_inv_map, assoc,
    Equivalence.counitInv_functor_comp, comp_id, Iso.inv_hom_id_app_assoc]
  rfl
def hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  toFun := hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm
end
section
variable (T : C₁ ⥤ C₂) (L : C₁ ≌ C₃) (R : C₂ ≌ C₄) (B : C₃ ⥤ C₄)
@[simps! iso'_hom_app iso'_inv_app]
def vInv (_ : CatCommSq T L.functor R.functor B) : CatCommSq B L.inverse R.inverse T where
  iso' := isoWhiskerRight (B.leftUnitor.symm ≪≫ isoWhiskerRight L.counitIso.symm B ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft L.inverse (iso T L.functor R.functor B).symm) R.inverse ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _ ).symm ≪≫ isoWhiskerLeft _ R.unitIso.symm ≪≫
      Functor.rightUnitor _
lemma vInv_vInv (h : CatCommSq T L.functor R.functor B) :
    vInv B L.symm R.symm T (vInv T L R B h) = h := by
  ext X
  erw [vInv_iso'_hom_app, vInv_iso'_inv_app]
  dsimp
  rw [← cancel_mono (B.map (L.functor.map (NatTrans.app L.unitIso.hom X)))]
  erw [← (iso T L.functor R.functor B).hom.naturality (L.unitIso.hom.app X)]
  dsimp
  simp only [Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj,
    Functor.id_obj, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, comp_id]
  erw [← B.map_comp, L.counit_app_functor, ← L.functor.map_comp, ← NatTrans.comp_app,
    Iso.inv_hom_id, NatTrans.id_app, L.functor.map_id, B.map_id, comp_id, R.counit_app_functor,
    ← R.functor.map_comp_assoc, ← R.functor.map_comp_assoc, assoc, ← NatTrans.comp_app,
    Iso.hom_inv_id, NatTrans.id_app, comp_id]
def vInvEquiv : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.inverse T where
  toFun := vInv T L R B
  invFun := vInv B L.symm R.symm T
  left_inv := vInv_vInv T L R B
  right_inv := vInv_vInv B L.symm R.symm T
end
end CatCommSq
end CategoryTheory