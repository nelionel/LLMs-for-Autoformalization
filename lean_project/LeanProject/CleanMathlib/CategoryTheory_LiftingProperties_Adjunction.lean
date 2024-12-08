import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
namespace CategoryTheory
open Category
variable {C D : Type*} [Category C] [Category D] {G : C ⥤ D} {F : D ⥤ C}
namespace CommSq
section
variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : G.obj A ⟶ X} {v : G.obj B ⟶ Y}
theorem right_adjoint (sq : CommSq u (G.map i) p v) (adj : G ⊣ F) :
    CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _ _ v) :=
  ⟨by
    simp only [Adjunction.homEquiv_unit, assoc, ← F.map_comp, sq.w]
    rw [F.map_comp, Adjunction.unit_naturality_assoc]⟩
variable (sq : CommSq u (G.map i) p v) (adj : G ⊣ F)
def rightAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.right_adjoint adj).LiftStruct where
  toFun l :=
    { l := adj.homEquiv _ _ l.l
      fac_left := by rw [← adj.homEquiv_naturality_left, l.fac_left]
      fac_right := by rw [← Adjunction.homEquiv_naturality_right, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by
        rw [← Adjunction.homEquiv_naturality_left_symm, l.fac_left]
        apply (adj.homEquiv _ _).left_inv
      fac_right := by
        rw [← Adjunction.homEquiv_naturality_right_symm, l.fac_right]
        apply (adj.homEquiv _ _).left_inv }
  left_inv := by aesop_cat
  right_inv := by aesop_cat
theorem right_adjoint_hasLift_iff : HasLift (sq.right_adjoint adj) ↔ HasLift sq := by
  simp only [HasLift.iff]
  exact Equiv.nonempty_congr (sq.rightAdjointLiftStructEquiv adj).symm
instance [HasLift sq] : HasLift (sq.right_adjoint adj) := by
  rw [right_adjoint_hasLift_iff]
  infer_instance
end
section
variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ F.obj X} {v : B ⟶ F.obj Y}
theorem left_adjoint (sq : CommSq u i (F.map p) v) (adj : G ⊣ F) :
    CommSq ((adj.homEquiv _ _).symm u) (G.map i) p ((adj.homEquiv _ _).symm v) :=
  ⟨by
    simp only [Adjunction.homEquiv_counit, assoc, ← G.map_comp_assoc, ← sq.w]
    rw [G.map_comp, assoc, Adjunction.counit_naturality]⟩
variable (sq : CommSq u i (F.map p) v) (adj : G ⊣ F)
def leftAdjointLiftStructEquiv :
    sq.LiftStruct ≃ (sq.left_adjoint adj).LiftStruct where
  toFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left := by rw [← adj.homEquiv_naturality_left_symm, l.fac_left]
      fac_right := by rw [← adj.homEquiv_naturality_right_symm, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _) l.l
      fac_left := by
        rw [← adj.homEquiv_naturality_left, l.fac_left]
        apply (adj.homEquiv _ _).right_inv
      fac_right := by
        rw [← adj.homEquiv_naturality_right, l.fac_right]
        apply (adj.homEquiv _ _).right_inv }
  left_inv := by aesop_cat
  right_inv := by aesop_cat
theorem left_adjoint_hasLift_iff : HasLift (sq.left_adjoint adj) ↔ HasLift sq := by
  simp only [HasLift.iff]
  exact Equiv.nonempty_congr (sq.leftAdjointLiftStructEquiv adj).symm
instance [HasLift sq] : HasLift (sq.left_adjoint adj) := by
  rw [left_adjoint_hasLift_iff]
  infer_instance
end
end CommSq
namespace Adjunction
theorem hasLiftingProperty_iff (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (G.map i) p ↔ HasLiftingProperty i (F.map p) := by
  constructor <;> intro <;> constructor <;> intro f g sq
  · rw [← sq.left_adjoint_hasLift_iff adj]
    infer_instance
  · rw [← sq.right_adjoint_hasLift_iff adj]
    infer_instance
end Adjunction
end CategoryTheory