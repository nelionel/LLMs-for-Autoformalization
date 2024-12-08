import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.HomCongr
import Mathlib.Tactic.ApplyFun
universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉
namespace CategoryTheory
open Category Functor Adjunction NatTrans
section mateEquiv
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
variable {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
@[simps]
def mateEquiv : (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) where
  toFun α :=
    whiskerLeft (R₁ ⋙ G) adj₂.unit ≫
    whiskerRight (whiskerLeft R₁ α) R₂ ≫
    whiskerRight adj₁.counit (H ⋙ R₂)
  invFun β :=
    whiskerRight adj₁.unit (G ⋙ L₂) ≫
    whiskerRight (whiskerLeft L₁ β) L₂ ≫
    whiskerLeft (L₁ ⋙ H) adj₂.counit
  left_inv α := by
    ext
    unfold whiskerRight whiskerLeft
    simp only [comp_obj, id_obj, Functor.comp_map, comp_app, map_comp, assoc, counit_naturality,
      counit_naturality_assoc, left_triangle_components_assoc]
    rw [← assoc, ← Functor.comp_map, α.naturality, Functor.comp_map, assoc, ← H.map_comp,
      left_triangle_components, map_id]
    simp only [comp_obj, comp_id]
  right_inv β := by
    ext
    unfold whiskerLeft whiskerRight
    simp only [comp_obj, id_obj, Functor.comp_map, comp_app, map_comp, assoc,
      unit_naturality_assoc, right_triangle_components_assoc]
    rw [← assoc, ← Functor.comp_map, assoc, ← β.naturality, ← assoc, Functor.comp_map,
      ← G.map_comp, right_triangle_components, map_id, id_comp]
@[deprecated (since := "2024-07-09")] alias transferNatTrans := mateEquiv
theorem mateEquiv_counit (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (d : D) :
    L₂.map ((mateEquiv adj₁ adj₂ α).app _) ≫ adj₂.counit.app _ =
      α.app _ ≫ H.map (adj₁.counit.app d) := by
  erw [Functor.map_comp]; simp
theorem mateEquiv_counit_symm (α : R₁ ⋙ G ⟶ H ⋙ R₂) (d : D) :
    L₂.map (α.app _) ≫ adj₂.counit.app _ =
      ((mateEquiv adj₁ adj₂).symm α).app _ ≫ H.map (adj₁.counit.app d) := by
  conv_lhs => rw [← (mateEquiv adj₁ adj₂).right_inv α]
  exact (mateEquiv_counit adj₁ adj₂ ((mateEquiv adj₁ adj₂).symm α) d)
theorem unit_mateEquiv (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (c : C) :
    G.map (adj₁.unit.app c) ≫ (mateEquiv adj₁ adj₂ α).app _ =
      adj₂.unit.app _ ≫ R₂.map (α.app _) := by
  dsimp [mateEquiv]
  rw [← adj₂.unit_naturality_assoc]
  slice_lhs 2 3 =>
    rw [← R₂.map_comp, ← Functor.comp_map G L₂, α.naturality]
  rw [R₂.map_comp]
  slice_lhs 3 4 =>
    rw [← R₂.map_comp, Functor.comp_map L₁ H, ← H.map_comp, left_triangle_components]
  simp only [comp_obj, map_id, comp_id]
theorem unit_mateEquiv_symm (α : R₁ ⋙ G ⟶ H ⋙ R₂) (c : C) :
    G.map (adj₁.unit.app c) ≫ α.app _ =
      adj₂.unit.app _ ≫ R₂.map (((mateEquiv adj₁ adj₂).symm α).app _) := by
  conv_lhs => rw [← (mateEquiv adj₁ adj₂).right_inv α]
  exact (unit_mateEquiv adj₁ adj₂ ((mateEquiv adj₁ adj₂).symm α) c)
end mateEquiv
section mateEquivVComp
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
def leftAdjointSquare.vcomp :
    (G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) → (G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) → ((G₁ ⋙ G₂) ⋙ L₃ ⟶ L₁ ⋙ (H₁ ⋙ H₂)) :=
  fun α β ↦ (whiskerLeft G₁ β) ≫ (whiskerRight α H₂)
def rightAdjointSquare.vcomp :
    (R₁ ⋙ G₁ ⟶ H₁ ⋙ R₂) → (R₂ ⋙ G₂ ⟶ H₂ ⋙ R₃) → (R₁ ⋙ (G₁ ⋙ G₂) ⟶ (H₁ ⋙ H₂) ⋙ R₃) :=
  fun α β ↦ (whiskerRight α G₂) ≫ (whiskerLeft H₁ β)
theorem mateEquiv_vcomp
    (α : G₁ ⋙ L₂ ⟶ L₁ ⋙ H₁) (β : G₂ ⋙ L₃ ⟶ L₂ ⋙ H₂) :
    (mateEquiv (G := G₁ ⋙ G₂) (H := H₁ ⋙ H₂) adj₁ adj₃) (leftAdjointSquare.vcomp α β) =
      rightAdjointSquare.vcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β) := by
  unfold leftAdjointSquare.vcomp rightAdjointSquare.vcomp mateEquiv
  ext b
  simp only [comp_obj, Equiv.coe_fn_mk, whiskerLeft_comp, whiskerLeft_twice, whiskerRight_comp,
    assoc, comp_app, whiskerLeft_app, whiskerRight_app, id_obj, Functor.comp_map,
    whiskerRight_twice]
  slice_rhs 1 4 => rw [← assoc, ← assoc, ← unit_naturality (adj₃)]
  rw [L₃.map_comp, R₃.map_comp]
  slice_rhs 2 4 =>
    rw [← R₃.map_comp, ← R₃.map_comp, ← assoc, ← L₃.map_comp, ← G₂.map_comp, ← G₂.map_comp]
    rw [← Functor.comp_map G₂ L₃, β.naturality]
  rw [(L₂ ⋙ H₂).map_comp, R₃.map_comp, R₃.map_comp]
  slice_rhs 4 5 =>
    rw [← R₃.map_comp, Functor.comp_map L₂ _, ← Functor.comp_map _ L₂, ← H₂.map_comp]
    rw [adj₂.counit.naturality]
  simp only [comp_obj, Functor.comp_map, map_comp, id_obj, Functor.id_map, assoc]
  slice_rhs 4 5 =>
    rw [← R₃.map_comp, ← H₂.map_comp, ← Functor.comp_map _ L₂, adj₂.counit.naturality]
  simp only [comp_obj, id_obj, Functor.id_map, map_comp, assoc]
  slice_rhs 3 4 =>
    rw [← R₃.map_comp, ← H₂.map_comp, left_triangle_components]
  simp only [map_id, id_comp]
end mateEquivVComp
section mateEquivHComp
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
variable {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
def leftAdjointSquare.hcomp :
    (G ⋙ L₂ ⟶ L₁ ⋙ H) → (H ⋙ L₄ ⟶ L₃ ⋙ K) → (G ⋙ (L₂ ⋙ L₄) ⟶ (L₁ ⋙ L₃) ⋙ K) := fun α β ↦
  (whiskerRight α L₄) ≫ (whiskerLeft L₁ β)
def rightAdjointSquare.hcomp :
    (R₁ ⋙ G ⟶ H ⋙ R₂) → (R₃ ⋙ H ⟶ K ⋙ R₄) → ((R₃ ⋙ R₁) ⋙ G ⟶ K ⋙ (R₄ ⋙ R₂)) := fun α β ↦
  (whiskerLeft R₃ α) ≫ (whiskerRight β R₂)
theorem mateEquiv_hcomp
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : H ⋙ L₄ ⟶ L₃ ⋙ K) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (leftAdjointSquare.hcomp α β) =
      rightAdjointSquare.hcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₃ adj₄ β) := by
  unfold leftAdjointSquare.hcomp rightAdjointSquare.hcomp mateEquiv Adjunction.comp
  ext c
  simp only [comp_obj, mk'_unit, whiskerLeft_comp, whiskerLeft_twice, mk'_counit, whiskerRight_comp,
    assoc, Equiv.coe_fn_mk, comp_app, whiskerLeft_app, whiskerRight_app, id_obj, associator_inv_app,
    Functor.comp_map, associator_hom_app, map_id, id_comp, whiskerRight_twice]
  slice_rhs 2 4 =>
    rw [← R₂.map_comp, ← R₂.map_comp, ← assoc, ← unit_naturality (adj₄)]
  rw [R₂.map_comp, L₄.map_comp, R₄.map_comp, R₂.map_comp]
  slice_rhs 4 5 =>
    rw [← R₂.map_comp, ← R₄.map_comp, ← Functor.comp_map _ L₄ , β.naturality]
  simp only [comp_obj, Functor.comp_map, map_comp, assoc]
end mateEquivHComp
section mateEquivSquareComp
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable {X : Type u₇} {Y : Type u₈} {Z : Type u₉}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable [Category.{v₇} X] [Category.{v₈} Y] [Category.{v₉} Z]
variable {G₁ : A ⥤ D} {H₁ : B ⥤ E} {K₁ : C ⥤ F} {G₂ : D ⥤ X} {H₂ : E ⥤ Y} {K₂ : F ⥤ Z}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : D ⥤ E} {R₃ : E ⥤ D}
variable {L₄ : E ⥤ F} {R₄ : F ⥤ E} {L₅ : X ⥤ Y} {R₅ : Y ⥤ X} {L₆ : Y ⥤ Z} {R₆ : Z ⥤ Y}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
variable (adj₄ : L₄ ⊣ R₄) (adj₅ : L₅ ⊣ R₅) (adj₆ : L₆ ⊣ R₆)
def leftAdjointSquare.comp
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    ((G₁ ⋙ G₂) ⋙ (L₅ ⋙ L₆)) ⟶ ((L₁ ⋙ L₂) ⋙ (K₁ ⋙ K₂)) :=
  leftAdjointSquare.vcomp (leftAdjointSquare.hcomp α β) (leftAdjointSquare.hcomp γ δ)
theorem leftAdjointSquare.comp_vhcomp
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    leftAdjointSquare.comp α β γ δ =
      leftAdjointSquare.vcomp (leftAdjointSquare.hcomp α β) (leftAdjointSquare.hcomp γ δ) := rfl
theorem leftAdjointSquare.comp_hvcomp
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    leftAdjointSquare.comp α β γ δ =
      leftAdjointSquare.hcomp (leftAdjointSquare.vcomp α γ) (leftAdjointSquare.vcomp β δ) := by
  unfold leftAdjointSquare.comp leftAdjointSquare.hcomp leftAdjointSquare.vcomp
  unfold whiskerLeft whiskerRight
  ext a
  simp only [comp_obj, comp_app, map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ L₆, δ.naturality]
  simp only [comp_obj, Functor.comp_map, assoc]
def rightAdjointSquare.comp
    (α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₃) (β : R₂ ⋙ H₁ ⟶ K₁ ⋙ R₄)
    (γ : R₃ ⋙ G₂ ⟶ H₂ ⋙ R₅) (δ : R₄ ⋙ H₂ ⟶ K₂ ⋙ R₆) :
    ((R₂ ⋙ R₁) ⋙ (G₁ ⋙ G₂) ⟶ (K₁ ⋙ K₂) ⋙ (R₆ ⋙ R₅)) :=
  rightAdjointSquare.vcomp (rightAdjointSquare.hcomp α β) (rightAdjointSquare.hcomp γ δ)
theorem rightAdjointSquare.comp_vhcomp
    (α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₃) (β : R₂ ⋙ H₁ ⟶ K₁ ⋙ R₄)
    (γ : R₃ ⋙ G₂ ⟶ H₂ ⋙ R₅) (δ : R₄ ⋙ H₂ ⟶ K₂ ⋙ R₆) :
    rightAdjointSquare.comp α β γ δ =
    rightAdjointSquare.vcomp (rightAdjointSquare.hcomp α β) (rightAdjointSquare.hcomp γ δ) := rfl
theorem rightAdjointSquare.comp_hvcomp
    (α : R₁ ⋙ G₁ ⟶ H₁ ⋙ R₃) (β : R₂ ⋙ H₁ ⟶ K₁ ⋙ R₄)
    (γ : R₃ ⋙ G₂ ⟶ H₂ ⋙ R₅) (δ : R₄ ⋙ H₂ ⟶ K₂ ⋙ R₆) :
    rightAdjointSquare.comp α β γ δ =
    rightAdjointSquare.hcomp (rightAdjointSquare.vcomp α γ) (rightAdjointSquare.vcomp β δ) := by
  unfold rightAdjointSquare.comp rightAdjointSquare.hcomp rightAdjointSquare.vcomp
  unfold whiskerLeft whiskerRight
  ext c
  simp only [comp_obj, comp_app, map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ R₅, ← γ.naturality]
  simp only [comp_obj, Functor.comp_map, assoc]
theorem mateEquiv_square
    (α : G₁ ⋙ L₃ ⟶ L₁ ⋙ H₁) (β : H₁ ⋙ L₄ ⟶ L₂ ⋙ K₁)
    (γ : G₂ ⋙ L₅ ⟶ L₃ ⋙ H₂) (δ : H₂ ⋙ L₆ ⟶ L₄ ⋙ K₂) :
    (mateEquiv (G := G₁ ⋙ G₂) (H := K₁ ⋙ K₂) (adj₁.comp adj₂) (adj₅.comp adj₆))
        (leftAdjointSquare.comp α β γ δ) =
      rightAdjointSquare.comp
        (mateEquiv adj₁ adj₃ α) (mateEquiv adj₂ adj₄ β)
        (mateEquiv adj₃ adj₅ γ) (mateEquiv adj₄ adj₆ δ) := by
  have vcomp :=
    mateEquiv_vcomp (adj₁.comp adj₂) (adj₃.comp adj₄) (adj₅.comp adj₆)
      (leftAdjointSquare.hcomp α β) (leftAdjointSquare.hcomp γ δ)
  have hcomp1 := mateEquiv_hcomp adj₁ adj₃ adj₂ adj₄ α β
  have hcomp2 := mateEquiv_hcomp adj₃ adj₅ adj₄ adj₆ γ δ
  rw [hcomp1, hcomp2] at vcomp
  exact vcomp
end mateEquivSquareComp
section conjugateEquiv
variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
@[simps!]
def conjugateEquiv : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
  calc
    (L₂ ⟶ L₁) ≃ _ := (Iso.homCongr L₂.leftUnitor L₁.rightUnitor).symm
    _ ≃ _ := mateEquiv adj₁ adj₂
    _ ≃ (R₁ ⟶ R₂) := R₁.rightUnitor.homCongr R₂.leftUnitor
@[deprecated (since := "2024-07-09")] alias transferNatTransSelf := conjugateEquiv
theorem conjugateEquiv_counit (α : L₂ ⟶ L₁) (d : D) :
    L₂.map ((conjugateEquiv adj₁ adj₂ α).app _) ≫ adj₂.counit.app d =
      α.app _ ≫ adj₁.counit.app d := by
  dsimp [conjugateEquiv]
  rw [id_comp, comp_id]
  have := mateEquiv_counit adj₁ adj₂ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv) d
  dsimp at this
  rw [this]
  simp only [comp_id, id_comp]
theorem conjugateEquiv_counit_symm (α : R₁ ⟶ R₂) (d : D) :
    L₂.map (α.app _) ≫ adj₂.counit.app d =
      ((conjugateEquiv adj₁ adj₂).symm α).app _ ≫ adj₁.counit.app d := by
    conv_lhs => rw [← (conjugateEquiv adj₁ adj₂).right_inv α]
    exact (conjugateEquiv_counit adj₁ adj₂ ((conjugateEquiv adj₁ adj₂).symm α) d)
theorem unit_conjugateEquiv (α : L₂ ⟶ L₁) (c : C) :
    adj₁.unit.app _ ≫ (conjugateEquiv adj₁ adj₂ α).app _ =
      adj₂.unit.app c ≫ R₂.map (α.app _) := by
  dsimp [conjugateEquiv]
  rw [id_comp, comp_id]
  have := unit_mateEquiv adj₁ adj₂ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv) c
  dsimp at this
  rw [this]
  simp
theorem unit_conjugateEquiv_symm (α : R₁ ⟶ R₂) (c : C) :
    adj₁.unit.app _ ≫ α.app _ =
      adj₂.unit.app c ≫ R₂.map (((conjugateEquiv adj₁ adj₂).symm α).app _) := by
    conv_lhs => rw [← (conjugateEquiv adj₁ adj₂).right_inv α]
    exact (unit_conjugateEquiv adj₁ adj₂ ((conjugateEquiv adj₁ adj₂).symm α) c)
@[simp]
theorem conjugateEquiv_id : conjugateEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _ := by
  ext
  dsimp [conjugateEquiv, mateEquiv]
  simp only [comp_id, map_id, id_comp, right_triangle_components]
@[simp]
theorem conjugateEquiv_symm_id : (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq]
  simp only [conjugateEquiv_id]
theorem conjugateEquiv_adjunction_id {L R : C ⥤ C} (adj : L ⊣ R) (α : 𝟭 C ⟶ L) (c : C) :
    (conjugateEquiv adj Adjunction.id α).app c = α.app (R.obj c) ≫ adj.counit.app c := by
  dsimp [conjugateEquiv, mateEquiv, Adjunction.id]
  simp only [comp_id, id_comp]
theorem conjugateEquiv_adjunction_id_symm {L R : C ⥤ C} (adj : L ⊣ R) (α : R ⟶ 𝟭 C) (c : C) :
    ((conjugateEquiv adj Adjunction.id).symm α).app c = adj.unit.app c ≫ α.app (L.obj c) := by
  dsimp [conjugateEquiv, mateEquiv, Adjunction.id]
  simp only [comp_id, id_comp]
end conjugateEquiv
section ConjugateComposition
variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
@[simp]
theorem conjugateEquiv_comp (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β =
      conjugateEquiv adj₁ adj₃ (β ≫ α) := by
  ext d
  dsimp [conjugateEquiv, mateEquiv]
  have vcomp := mateEquiv_vcomp adj₁ adj₂ adj₃
    (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv)
    (L₃.leftUnitor.hom ≫ β ≫ L₂.rightUnitor.inv)
  have vcompd := congr_app vcomp d
  dsimp [mateEquiv, leftAdjointSquare.vcomp, rightAdjointSquare.vcomp] at vcompd
  simp only [comp_id, id_comp, assoc, map_comp] at vcompd ⊢
  rw [vcompd]
@[simp]
theorem conjugateEquiv_symm_comp (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) :
    (conjugateEquiv adj₂ adj₃).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α =
      (conjugateEquiv adj₁ adj₃).symm (α ≫ β) := by
  rw [Equiv.eq_symm_apply, ← conjugateEquiv_comp _ adj₂]
  simp only [Equiv.apply_symm_apply]
theorem conjugateEquiv_comm {α : L₂ ⟶ L₁} {β : L₁ ⟶ L₂} (βα : β ≫ α = 𝟙 _) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₁ β = 𝟙 _ := by
  rw [conjugateEquiv_comp, βα, conjugateEquiv_id]
theorem conjugateEquiv_symm_comm {α : R₁ ⟶ R₂} {β : R₂ ⟶ R₁} (αβ : α ≫ β = 𝟙 _) :
    (conjugateEquiv adj₂ adj₁).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α = 𝟙 _ := by
  rw [conjugateEquiv_symm_comp, αβ, conjugateEquiv_symm_id]
end ConjugateComposition
section ConjugateIsomorphism
variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
instance conjugateEquiv_iso (α : L₂ ⟶ L₁) [IsIso α] :
    IsIso (conjugateEquiv adj₁ adj₂ α) :=
  ⟨⟨conjugateEquiv adj₂ adj₁ (inv α),
      ⟨conjugateEquiv_comm _ _ (by simp), conjugateEquiv_comm _ _ (by simp)⟩⟩⟩
instance conjugateEquiv_symm_iso (α : R₁ ⟶ R₂) [IsIso α] :
    IsIso ((conjugateEquiv adj₁ adj₂).symm α) :=
  ⟨⟨(conjugateEquiv adj₂ adj₁).symm (inv α),
      ⟨conjugateEquiv_symm_comm _ _ (by simp), conjugateEquiv_symm_comm _ _ (by simp)⟩⟩⟩
theorem conjugateEquiv_of_iso (α : L₂ ⟶ L₁) [IsIso (conjugateEquiv adj₁ adj₂ α)] :
    IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂).symm (conjugateEquiv adj₁ adj₂ α))
    by simpa using this
  infer_instance
theorem conjugateEquiv_symm_of_iso (α : R₁ ⟶ R₂)
    [IsIso ((conjugateEquiv adj₁ adj₂).symm α)] : IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂) ((conjugateEquiv adj₁ adj₂).symm α))
    by simpa using this
  infer_instance
@[simps]
def conjugateIsoEquiv : (L₂ ≅ L₁) ≃ (R₁ ≅ R₂) where
  toFun α := {
    hom := conjugateEquiv adj₁ adj₂ α.hom
    inv := conjugateEquiv adj₂ adj₁ α.inv
  }
  invFun β := {
    hom := (conjugateEquiv adj₁ adj₂).symm β.hom
    inv := (conjugateEquiv adj₂ adj₁).symm β.inv
  }
  left_inv := by aesop_cat
  right_inv := by aesop_cat
end ConjugateIsomorphism
section IteratedmateEquiv
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
variable {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
theorem iterated_mateEquiv_conjugateEquiv (α : F₁ ⋙ L₂ ⟶ L₁ ⋙ F₂) :
    mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α) =
      conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α := by
  ext d
  unfold conjugateEquiv mateEquiv Adjunction.comp
  simp
theorem iterated_mateEquiv_conjugateEquiv_symm (α : U₂ ⋙ R₁ ⟶ R₂ ⋙ U₁) :
    (mateEquiv adj₁ adj₂).symm ((mateEquiv adj₄ adj₃).symm α) =
      (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)).symm α := by
  rw [Equiv.eq_symm_apply, ← iterated_mateEquiv_conjugateEquiv]
  simp only [Equiv.apply_symm_apply]
end IteratedmateEquiv
section mateEquivconjugateEquivVComp
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D]
variable {G : A ⥤ C} {H : B ⥤ D}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : C ⥤ D} {R₃ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
def leftAdjointSquareConjugate.vcomp :
    (G ⋙ L₂ ⟶ L₁ ⋙ H) → (L₃ ⟶ L₂) → (G ⋙ L₃ ⟶ L₁ ⋙ H) :=
  fun α β ↦ (whiskerLeft G β) ≫ α
def rightAdjointSquareConjugate.vcomp :
    (R₁ ⋙ G ⟶ H ⋙ R₂) → (R₂ ⟶ R₃) → (R₁ ⋙ G ⟶ H ⋙ R₃) :=
  fun α β ↦ α ≫ (whiskerLeft H β)
theorem mateEquiv_conjugateEquiv_vcomp
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : L₃ ⟶ L₂) :
    (mateEquiv adj₁ adj₃) (leftAdjointSquareConjugate.vcomp α β) =
      rightAdjointSquareConjugate.vcomp (mateEquiv adj₁ adj₂ α) (conjugateEquiv adj₂ adj₃ β) := by
  ext b
  have vcomp := mateEquiv_vcomp adj₁ adj₂ adj₃ α (L₃.leftUnitor.hom ≫ β ≫ L₂.rightUnitor.inv)
  unfold leftAdjointSquare.vcomp rightAdjointSquare.vcomp at vcomp
  unfold leftAdjointSquareConjugate.vcomp rightAdjointSquareConjugate.vcomp conjugateEquiv
  have vcompb := congr_app vcomp b
  simp at vcompb
  unfold mateEquiv
  simp only [comp_obj, Equiv.coe_fn_mk, whiskerLeft_comp, whiskerLeft_twice, whiskerRight_comp,
    assoc, comp_app, whiskerLeft_app, whiskerRight_app, id_obj, Functor.comp_map, Iso.homCongr_symm,
    Equiv.instTrans_trans, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
    rightUnitor_inv_app, leftUnitor_hom_app, map_id, Functor.id_map, comp_id, id_comp]
  exact vcompb
end mateEquivconjugateEquivVComp
section conjugateEquivmateEquivVComp
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D]
variable {G : A ⥤ C} {H : B ⥤ D}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : A ⥤ B} {R₂ : B ⥤ A} {L₃ : C ⥤ D} {R₃ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
def leftAdjointConjugateSquare.vcomp :
    (L₂ ⟶ L₁) → (G ⋙ L₃ ⟶ L₂ ⋙ H) → (G ⋙ L₃ ⟶ L₁ ⋙ H) :=
  fun α β ↦ β ≫ (whiskerRight α H)
def rightAdjointConjugateSquare.vcomp :
    (R₁ ⟶ R₂) → (R₂ ⋙ G ⟶ H ⋙ R₃) → (R₁ ⋙ G ⟶ H ⋙ R₃) :=
  fun α β ↦ (whiskerRight α G) ≫ β
theorem conjugateEquiv_mateEquiv_vcomp
    (α : L₂ ⟶ L₁) (β : G ⋙ L₃ ⟶ L₂ ⋙ H) :
    (mateEquiv adj₁ adj₃) (leftAdjointConjugateSquare.vcomp α β) =
      rightAdjointConjugateSquare.vcomp (conjugateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β) := by
  ext b
  have vcomp := mateEquiv_vcomp adj₁ adj₂ adj₃ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv) β
  unfold leftAdjointSquare.vcomp rightAdjointSquare.vcomp at vcomp
  unfold leftAdjointConjugateSquare.vcomp rightAdjointConjugateSquare.vcomp conjugateEquiv
  have vcompb := congr_app vcomp b
  simp at vcompb
  unfold mateEquiv
  simp only [comp_obj, Equiv.coe_fn_mk, whiskerLeft_comp, whiskerLeft_twice, whiskerRight_comp,
    assoc, comp_app, whiskerLeft_app, whiskerRight_app, id_obj, Functor.comp_map, Iso.homCongr_symm,
    Equiv.instTrans_trans, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
    rightUnitor_inv_app, leftUnitor_hom_app, map_id, Functor.id_map, comp_id, id_comp]
  exact vcompb
end conjugateEquivmateEquivVComp
end CategoryTheory