import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Localization.Predicate
namespace CategoryTheory
namespace Functor
variable {C C' D D' H H' : Type _} [Category C] [Category C']
  [Category D] [Category D'] [Category H] [Category H']
  (RF RF' RF'' : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (α'' : F'' ⟶ L ⋙ RF'') (α'₂ : F ⟶ L ⋙ RF')
  (W : MorphismProperty C)
class IsRightDerivedFunctor [L.IsLocalization W] : Prop where
  isLeftKanExtension' : RF.IsLeftKanExtension α
lemma IsRightDerivedFunctor.isLeftKanExtension
    [L.IsLocalization W] [RF.IsRightDerivedFunctor α W] :
    RF.IsLeftKanExtension α :=
  IsRightDerivedFunctor.isLeftKanExtension' W
lemma isRightDerivedFunctor_iff_isLeftKanExtension [L.IsLocalization W] :
    RF.IsRightDerivedFunctor α W ↔ RF.IsLeftKanExtension α := by
  constructor
  · exact fun _ => IsRightDerivedFunctor.isLeftKanExtension RF α W
  · exact fun h => ⟨h⟩
variable {RF RF'} in
lemma isRightDerivedFunctor_iff_of_iso (α' : F ⟶ L ⋙ RF') (W : MorphismProperty C)
    [L.IsLocalization W] (e : RF ≅ RF') (comm : α ≫ whiskerLeft L e.hom = α') :
    RF.IsRightDerivedFunctor α W ↔ RF'.IsRightDerivedFunctor α' W := by
  simp only [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact isLeftKanExtension_iff_of_iso e _ _ comm
section
variable [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]
noncomputable def rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) : RF ⟶ G :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension α G β
@[reassoc (attr := simp)]
lemma rightDerived_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β) = β :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac α G β
@[reassoc (attr := simp)]
lemma rightDerived_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (RF.rightDerivedDesc α W G β).app (L.obj X) = β.app X :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.descOfIsLeftKanExtension_fac_app α G β X
include W in
lemma rightDerived_ext (G : D ⥤ H) (γ₁ γ₂ : RF ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  RF.hom_ext_of_isLeftKanExtension α γ₁ γ₂ hγ
noncomputable def rightDerivedNatTrans (τ : F ⟶ F') : RF ⟶ RF' :=
  RF.rightDerivedDesc α W RF' (τ ≫ α')
@[reassoc (attr := simp)]
lemma rightDerivedNatTrans_fac (τ : F ⟶ F') :
    α ≫ whiskerLeft L (rightDerivedNatTrans RF RF' α α' W τ) = τ ≫ α' := by
  dsimp only [rightDerivedNatTrans]
  simp
@[reassoc (attr := simp)]
lemma rightDerivedNatTrans_app (τ : F ⟶ F') (X : C) :
    α.app X ≫ (rightDerivedNatTrans RF RF' α α' W τ).app (L.obj X) =
    τ.app X ≫ α'.app X := by
  dsimp only [rightDerivedNatTrans]
  simp
@[simp]
lemma rightDerivedNatTrans_id :
    rightDerivedNatTrans RF RF α α W (𝟙 F) = 𝟙 RF :=
  rightDerived_ext RF α W _ _ _ (by aesop_cat)
variable [RF'.IsRightDerivedFunctor α' W]
@[reassoc (attr := simp)]
lemma rightDerivedNatTrans_comp (τ : F ⟶ F') (τ' : F' ⟶ F'') :
    rightDerivedNatTrans RF RF' α α' W τ ≫ rightDerivedNatTrans RF' RF'' α' α'' W τ' =
    rightDerivedNatTrans RF RF'' α α'' W (τ ≫ τ') :=
  rightDerived_ext RF α W _ _ _ (by aesop_cat)
@[simps]
noncomputable def rightDerivedNatIso (τ : F ≅ F') :
    RF ≅ RF' where
  hom := rightDerivedNatTrans RF RF' α α' W τ.hom
  inv := rightDerivedNatTrans RF' RF α' α W τ.inv
noncomputable abbrev rightDerivedUnique [RF'.IsRightDerivedFunctor α'₂ W] : RF ≅ RF' :=
  rightDerivedNatIso RF RF' α α'₂ W (Iso.refl F)
lemma isRightDerivedFunctor_iff_isIso_rightDerivedDesc (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    G.IsRightDerivedFunctor β W ↔ IsIso (RF.rightDerivedDesc α W G β) := by
  rw [isRightDerivedFunctor_iff_isLeftKanExtension]
  have := IsRightDerivedFunctor.isLeftKanExtension _ α W
  exact isLeftKanExtension_iff_isIso _ α _ (by simp)
end
variable (F)
class HasRightDerivedFunctor : Prop where
  hasLeftKanExtension' : HasLeftKanExtension W.Q F
variable (L)
variable [L.IsLocalization W]
lemma hasRightDerivedFunctor_iff :
    F.HasRightDerivedFunctor W ↔ HasLeftKanExtension L F := by
  have : HasRightDerivedFunctor F W ↔ HasLeftKanExtension W.Q F :=
    ⟨fun h => h.hasLeftKanExtension', fun h => ⟨h⟩⟩
  rw [this, hasLeftExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]
variable {F}
include e in
lemma hasRightDerivedFunctor_iff_of_iso :
    HasRightDerivedFunctor F W ↔ HasRightDerivedFunctor F' W := by
  rw [hasRightDerivedFunctor_iff F W.Q W, hasRightDerivedFunctor_iff F' W.Q W,
    hasLeftExtension_iff_of_iso₂ W.Q e]
variable (F)
lemma HasRightDerivedFunctor.hasLeftKanExtension [HasRightDerivedFunctor F W] :
    HasLeftKanExtension L F := by
  simpa only [← hasRightDerivedFunctor_iff F L W]
variable {F L W}
lemma HasRightDerivedFunctor.mk' [RF.IsRightDerivedFunctor α W] :
    HasRightDerivedFunctor F W := by
  have := IsRightDerivedFunctor.isLeftKanExtension RF α W
  simpa only [hasRightDerivedFunctor_iff F L W] using HasLeftKanExtension.mk RF α
section
variable [F.HasRightDerivedFunctor W] (L W)
noncomputable def totalRightDerived : D ⥤ H :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtension L F
noncomputable def totalRightDerivedUnit : F ⟶ L ⋙ F.totalRightDerived L W :=
  have := HasRightDerivedFunctor.hasLeftKanExtension F L W
  leftKanExtensionUnit L F
instance : (F.totalRightDerived L W).IsRightDerivedFunctor
    (F.totalRightDerivedUnit L W) W where
  isLeftKanExtension' := by
    dsimp [totalRightDerived, totalRightDerivedUnit]
    infer_instance
end
end Functor
end CategoryTheory