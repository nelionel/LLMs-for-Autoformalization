import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Iso
namespace CategoryTheory
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
open NatTrans Category CategoryTheory.Functor
variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
attribute [local simp] vcomp_app
variable {C D} {E : Type u₃} [Category.{v₃} E]
variable {E' : Type u₄} [Category.{v₄} E']
variable {F G H I : C ⥤ D}
instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
namespace NatTrans
@[ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w
@[simp]
theorem vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β := rfl
theorem vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X := rfl
theorem congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by rw [h]
@[simp]
theorem id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl
@[simp]
theorem comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl
attribute [reassoc] comp_app
@[reassoc]
theorem app_naturality {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f :=
  (T.app X).naturality f
@[reassoc]
theorem naturality_app {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z :=
  congr_fun (congr_arg app (T.naturality f)) Z
@[reassoc]
theorem naturality_app_app {F G : C ⥤ D ⥤ E ⥤ E'}
    (α : F ⟶ G) {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ : D) (X₃ : E) :
    ((F.map f).app X₂).app X₃ ≫ ((α.app Y₁).app X₂).app X₃ =
      ((α.app X₁).app X₂).app X₃ ≫ ((G.map f).app X₂).app X₃ :=
  congr_app (NatTrans.naturality_app α X₂ f) X₃
theorem mono_of_mono_app (α : F ⟶ G) [∀ X : C, Mono (α.app X)] : Mono α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_mono (α.app X), ← comp_app, eq, comp_app]⟩
theorem epi_of_epi_app (α : F ⟶ G) [∀ X : C, Epi (α.app X)] : Epi α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_epi (α.app X), ← comp_app, eq, comp_app]⟩
lemma id_comm (α β : (𝟭 C) ⟶ (𝟭 C)) : α ≫ β = β ≫ α := by
  ext X
  exact (α.naturality (β.app X)).symm
@[simps]
def hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : F ⋙ H ⟶ G ⋙ I where
  app := fun X : C => β.app (F.obj X) ≫ I.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map, Functor.comp_map, ← assoc, naturality, assoc, ← map_comp I, naturality,
      map_comp, assoc]
infixl:80 " ◫ " => hcomp
theorem hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.app X) := by
  simp
theorem id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _ := by simp
theorem exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ β ◫ δ := by
  aesop_cat
end NatTrans
open NatTrans
namespace Functor
@[simps]
protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }
end Functor
namespace Iso
@[reassoc (attr := simp)]
theorem map_hom_inv_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← Functor.map_comp]
@[reassoc (attr := simp)]
theorem map_inv_hom_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ := by
  simp [← NatTrans.comp_app, ← Functor.map_comp]
end Iso
@[deprecated (since := "2024-06-09")] alias map_hom_inv_app := Iso.map_hom_inv_id_app
@[deprecated (since := "2024-06-09")] alias map_inv_hom_app := Iso.map_inv_hom_id_app
@[deprecated (since := "2024-06-09")] alias map_hom_inv_app_assoc := Iso.map_hom_inv_id_app_assoc
@[deprecated (since := "2024-06-09")] alias map_inv_hom_app_assoc := Iso.map_inv_hom_id_app_assoc
end CategoryTheory