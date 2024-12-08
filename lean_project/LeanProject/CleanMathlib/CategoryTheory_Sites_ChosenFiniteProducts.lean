import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open Opposite CategoryTheory Category Limits Sieve MonoidalCategory
variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)
variable [ChosenFiniteProducts A]
namespace Sheaf
variable (X Y : Sheaf J A)
lemma tensorProd_isSheaf : Presheaf.IsSheaf J (X.val ⊗ Y.val) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (ChosenFiniteProducts.product X.val Y.val).cone)
  exact (IsLimit.postcomposeInvEquiv _ _).invFun (ChosenFiniteProducts.product X.val Y.val).isLimit
lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (Functor.uniqueFromEmpty _).inv).obj
    ChosenFiniteProducts.terminal.cone)
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun ChosenFiniteProducts.terminal.isLimit
  · exact Functor.empty _
@[simps! product_cone_pt_val terminal_cone_pt_val_obj terminal_cone_pt_val_map]
noncomputable instance chosenFiniteProducts : ChosenFiniteProducts (Sheaf J A) where
  product X Y :=
    { cone := BinaryFan.mk
          (P := { val := X.val ⊗ Y.val
                  cond := tensorProd_isSheaf J X Y})
          ⟨(ChosenFiniteProducts.fst _ _)⟩ ⟨(ChosenFiniteProducts.snd _ _)⟩
      isLimit :=
        { lift := fun f ↦ ⟨ChosenFiniteProducts.lift (BinaryFan.fst f).val (BinaryFan.snd f).val⟩
          fac := by rintro s ⟨⟨j⟩⟩ <;> apply Sheaf.hom_ext <;> simp
          uniq := by
            intro x f h
            apply Sheaf.hom_ext
            apply ChosenFiniteProducts.hom_ext
            · specialize h ⟨WalkingPair.left⟩
              rw [Sheaf.hom_ext_iff] at h
              simpa using h
            · specialize h ⟨WalkingPair.right⟩
              rw [Sheaf.hom_ext_iff] at h
              simpa using h } }
  terminal :=
    { cone := asEmptyCone { val := 𝟙_ (Cᵒᵖ ⥤ A)
                            cond := tensorUnit_isSheaf _}
      isLimit :=
        { lift := fun f ↦ ⟨ChosenFiniteProducts.toUnit f.pt.val⟩
          fac := by intro s ⟨e⟩; cases e
          uniq := by
            intro x f h
            apply Sheaf.hom_ext
            exact ChosenFiniteProducts.toUnit_unique f.val _} }
@[simp]
lemma chosenFiniteProducts_fst_val : (ChosenFiniteProducts.fst X Y).val =
    ChosenFiniteProducts.fst X.val Y.val := rfl
@[simp]
lemma chosenFiniteProducts_snd_val : (ChosenFiniteProducts.snd X Y).val =
    ChosenFiniteProducts.snd X.val Y.val := rfl
variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)
@[simp]
lemma chosenFiniteProducts_lift_val : (ChosenFiniteProducts.lift f g).val =
    ChosenFiniteProducts.lift f.val g.val := rfl
@[simp]
lemma chosenFiniteProducts_whiskerLeft_val : (X ◁ f).val = (X.val ◁ f.val) := rfl
@[simp]
lemma chosenFiniteProducts_whiskerRight_val : (f ▷ X).val = (f.val ▷ X.val) := rfl
end Sheaf
noncomputable instance sheafToPresheafMonoidal : (sheafToPresheaf J A).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun F G ↦ Iso.refl _ }
open Functor.LaxMonoidal Functor.OplaxMonoidal
@[simp]
lemma sheafToPresheaf_ε : ε (sheafToPresheaf J A) = 𝟙 _ := rfl
@[simp]
lemma sheafToPresheaf_η : η (sheafToPresheaf J A) = 𝟙 _ := rfl
variable {J}
@[simp]
lemma sheafToPresheaf_μ (X Y : Sheaf J A) : μ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
@[simp]
lemma sheafToPresheaf_δ (X Y : Sheaf J A) : δ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
end CategoryTheory