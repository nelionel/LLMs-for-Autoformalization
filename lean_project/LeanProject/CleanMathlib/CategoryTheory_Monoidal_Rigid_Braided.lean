import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
open CategoryTheory Category BraidedCategory MonoidalCategory
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {X Y : C}
namespace CategoryTheory.BraidedCategory
private theorem coevaluation_evaluation_braided' [inst : ExactPairing X Y] :
    X ◁ (η_ X Y ≫ (β_ Y X).inv) ≫ (α_ X Y X).inv ≫ ((β_ X Y).hom ≫ ε_ X Y) ▷ X
      = (ρ_ X).hom ≫ (λ_ X).inv := by
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (X ◁ (β_ Y X).inv ⊗≫ (β_ X Y).hom ▷ X) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
      monoidal
    _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (𝟙 (X ⊗ X ⊗ Y) ⊗≫ (β_ X X).hom ▷ Y ⊗≫ X ◁ (β_ X Y).hom
          ⊗≫ (β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ 𝟙 ((Y ⊗ X) ⊗ X)) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
      congr 3
      simp only [monoidalComp, MonoidalCoherence.assoc'_iso, MonoidalCoherence.whiskerRight_iso,
        MonoidalCoherence.refl_iso, whiskerRightIso_refl, Iso.refl_trans, Iso.symm_hom,
        MonoidalCoherence.assoc_iso, Iso.trans_refl, comp_id, id_comp]
      rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 5 rw [← IsIso.comp_inv_eq]
      simpa using yang_baxter X Y X
    _ = 𝟙 X ⊗≫ (X ◁ η_ X Y ≫ (β_ X (X ⊗ Y)).hom) ⊗≫ ((β_ (Y ⊗ X) X).inv ≫ ε_ X Y ▷ X) ⊗≫ 𝟙 X := by
      simp [monoidalComp, braiding_tensor_right, braiding_inv_tensor_left]
    _ = _ := by
      rw [braiding_naturality_right, ← braiding_inv_naturality_right]
      simp [monoidalComp]
private theorem evaluation_coevaluation_braided' [inst : ExactPairing X Y] :
    (η_ X Y ≫ (β_ Y X).inv) ▷ Y ≫ (α_ Y X Y).hom ≫ Y ◁ ((β_ X Y).hom ≫ ε_ X Y) =
      (λ_ Y).hom ≫ (ρ_ Y).inv := by
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 Y ⊗≫ η_ X Y ▷ Y ⊗≫ ((β_ Y X).inv ▷ Y ⊗≫ Y ◁ (β_ X Y).hom) ≫ Y ◁ ε_ X Y ⊗≫ 𝟙 Y := by
      monoidal
    _ = 𝟙 Y ⊗≫ η_ X Y ▷ Y ⊗≫ (𝟙 ((X ⊗ Y) ⊗ Y) ⊗≫ X ◁ (β_ Y Y).hom ⊗≫ (β_ X Y).hom ▷ Y
        ⊗≫ Y ◁ (β_ Y X).inv ⊗≫ (β_ Y Y).inv ▷ X ⊗≫ 𝟙 (Y ⊗ Y ⊗ X)) ⊗≫ Y ◁ ε_ X Y ⊗≫ 𝟙 Y := by
      congr 3
      all_goals simp [monoidalComp]
      iterate 2 rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 4 rw [← IsIso.comp_inv_eq]
      simpa using (yang_baxter Y X Y).symm
    _ = 𝟙 Y ⊗≫ (η_ X Y ▷ Y ≫ (β_ (X ⊗ Y) Y).hom) ⊗≫ ((β_ Y (Y ⊗ X)).inv ≫ Y ◁ ε_ X Y) ⊗≫ 𝟙 Y := by
      simp [monoidalComp, braiding_tensor_left, braiding_inv_tensor_right]
    _ = _ := by
      rw [braiding_naturality_left, ← braiding_inv_naturality_left]
      simp [monoidalComp]
def exactPairing_swap (X Y : C) [ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := η_ X Y ≫ (β_ Y X).inv
  evaluation' := (β_ X Y).hom ≫ ε_ X Y
  coevaluation_evaluation' := coevaluation_evaluation_braided'
  evaluation_coevaluation' := evaluation_coevaluation_braided'
def hasLeftDualOfHasRightDual [HasRightDual X] : HasLeftDual X where
  leftDual := Xᘁ
  exact := exactPairing_swap X Xᘁ
def hasRightDualOfHasLeftDual [HasLeftDual X] : HasRightDual X where
  rightDual := ᘁX
  exact := exactPairing_swap ᘁX X
instance leftRigidCategoryOfRightRigidCategory [RightRigidCategory C] : LeftRigidCategory C where
  leftDual X := hasLeftDualOfHasRightDual (X := X)
instance rightRigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RightRigidCategory C where
  rightDual X := hasRightDualOfHasLeftDual (X := X)
instance rigidCategoryOfRightRigidCategory [RightRigidCategory C] : RigidCategory C where
  rightDual := inferInstance
  leftDual := inferInstance
instance rigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RigidCategory C where
  rightDual := inferInstance
  leftDual := inferInstance
end CategoryTheory.BraidedCategory