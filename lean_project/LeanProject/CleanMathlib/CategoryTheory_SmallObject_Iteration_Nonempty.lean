import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
universe u
namespace CategoryTheory
open Category Limits
variable {C : Type*} [Category C] {Φ : C ⥤ C} {ε : 𝟭 C ⟶ Φ}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
namespace Functor
namespace Iteration
variable (ε J) in
def mkOfBot : Iteration ε (⊥ : J) where
  F := (Functor.const _).obj (𝟭 C)
  isoZero := Iso.refl _
  isoSucc _ h := by simp at h
  mapSucc'_eq _ h := by simp at h
  isColimit x hx h := by
    exfalso
    refine hx.not_isMin (by simpa using h)
noncomputable def mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Iteration ε j) :
    Iteration ε (Order.succ j) where
  F := extendToSucc hj iter.F (whiskerLeft _ ε)
  isoZero := (extendToSuccObjIso hj iter.F (whiskerLeft _ ε) ⟨⊥, by simp⟩).trans iter.isoZero
  isoSucc i hi :=
    if hij : i < j then
      extendToSuccObjIso _ _ _ ⟨Order.succ i, Order.succ_le_of_lt hij⟩ ≪≫
        iter.isoSucc i hij ≪≫ (isoWhiskerRight (extendToSuccObjIso _ _ _ ⟨i, hij.le⟩).symm _)
    else
      have hij' : i = j := le_antisymm
        (by simpa only [Order.lt_succ_iff_of_not_isMax hj] using hi) (by simpa using hij)
      eqToIso (by subst hij'; rfl) ≪≫ extendToSuccObjSuccIso hj iter.F (whiskerLeft _ ε) ≪≫
        isoWhiskerRight ((extendToSuccObjIso hj iter.F (whiskerLeft _ ε) ⟨j, by simp⟩).symm.trans
            (eqToIso (by subst hij'; rfl))) _
  mapSucc'_eq i hi := by
    obtain hi' | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hi).lt_or_eq
    · ext X
      have := iter.mapSucc_eq i hi'
      dsimp [mapSucc, mapSucc'] at this ⊢
      rw [extentToSucc_map _ _ _ _ _ _ (Order.succ_le_of_lt hi'), this, dif_pos hi']
      dsimp
      rw [assoc, assoc]
      erw [ε.naturality_assoc]
    · ext X
      dsimp [mapSucc']
      rw [dif_neg (gt_irrefl i), extendToSucc_map_le_succ]
      dsimp
      rw [id_comp, comp_id]
      erw [ε.naturality_assoc]
  isColimit i hi hij := by
    have hij' : i ≤ j := by
      obtain hij | rfl := hij.lt_or_eq
      · exact (Order.lt_succ_iff_of_not_isMax hj).1 hij
      · exfalso
        exact Order.not_isSuccLimit_succ_of_not_isMax hj hi
    refine (IsColimit.precomposeHomEquiv
      (isoWhiskerLeft (monotone_inclusion_lt_le_of_le hij').functor
        (extendToSuccRestrictionLEIso hj iter.F (whiskerLeft _ ε))).symm _).1
      (IsColimit.ofIsoColimit (iter.isColimit i hi hij')
      (Iso.symm (Cocones.ext (extendToSuccObjIso hj iter.F (whiskerLeft _ ε) ⟨i, hij'⟩)
      (fun ⟨k, hk⟩ ↦ ?_))))
    dsimp
    rw [assoc, extendToSuccObjIso_hom_naturality hj iter.F (whiskerLeft _ ε)]
    dsimp
    rw [Iso.inv_hom_id_assoc]
end Iteration
end Functor
end CategoryTheory