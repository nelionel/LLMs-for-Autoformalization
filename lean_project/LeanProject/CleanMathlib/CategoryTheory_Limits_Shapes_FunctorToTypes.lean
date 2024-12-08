import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types
open CategoryTheory.Limits
universe w v u
namespace CategoryTheory.FunctorToTypes
variable {C : Type u} [Category.{v} C]
variable (F G : C ⥤ Type w)
section prod
def prod : C ⥤ Type w where
  obj a := F.obj a × G.obj a
  map f a := (F.map f a.1, G.map f a.2)
variable {F G}
@[simps]
def prod.fst : prod F G ⟶ F where
  app _ a := a.1
@[simps]
def prod.snd : prod F G ⟶ G where
  app _ a := a.2
@[simps]
def prod.lift {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ prod F₁ F₂ where
  app x y := ⟨τ₁.app x y, τ₂.app x y⟩
  naturality _ _ _ := by
    ext a
    simp only [types_comp_apply, FunctorToTypes.naturality]
    aesop
@[simp]
lemma prod.lift_fst {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.fst = τ₁ := rfl
@[simp]
lemma prod.lift_snd {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.snd = τ₂ := rfl
variable (F G)
@[simps!]
def binaryProductCone : BinaryFan F G :=
  BinaryFan.mk prod.fst prod.snd
@[simps]
def binaryProductLimit : IsLimit (binaryProductCone F G) where
  lift (s : BinaryFan F G) := prod.lift s.fst s.snd
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    simp only [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
    congr
def binaryProductLimitCone : Limits.LimitCone (pair F G) :=
  ⟨_, binaryProductLimit F G⟩
noncomputable def binaryProductIso : F ⨯ G ≅ prod F G :=
  limit.isoLimitCone (binaryProductLimitCone F G)
@[simp]
lemma binaryProductIso_hom_comp_fst :
    (binaryProductIso F G).hom ≫ prod.fst = Limits.prod.fst := rfl
@[simp]
lemma binaryProductIso_hom_comp_snd :
    (binaryProductIso F G).hom ≫ prod.snd = Limits.prod.snd := rfl
@[simp]
lemma binaryProductIso_inv_comp_fst :
    (binaryProductIso F G).inv ≫ Limits.prod.fst = prod.fst := by
  simp [binaryProductIso, binaryProductLimitCone]
@[simp]
lemma binaryProductIso_inv_comp_fst_apply (a : C) (z : (prod F G).obj a) :
    (Limits.prod.fst (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.1 :=
  congr_fun (congr_app (binaryProductIso_inv_comp_fst F G) a) z
@[simp]
lemma binaryProductIso_inv_comp_snd :
    (binaryProductIso F G).inv ≫ Limits.prod.snd = prod.snd := by
  simp [binaryProductIso, binaryProductLimitCone]
@[simp]
lemma binaryProductIso_inv_comp_snd_apply (a : C) (z : (prod F G).obj a) :
    (Limits.prod.snd (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.2 :=
  congr_fun (congr_app (binaryProductIso_inv_comp_snd F G) a) z
variable {F G}
noncomputable
def prodMk {a : C} (x : F.obj a) (y : G.obj a) : (F ⨯ G).obj a :=
  ((binaryProductIso F G).inv).app a ⟨x, y⟩
@[simp]
lemma prodMk_fst {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.fst (X := F)).app a (prodMk x y) = x := by
  simp only [prodMk, binaryProductIso_inv_comp_fst_apply]
@[simp]
lemma prodMk_snd {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.snd (X := F)).app a (prodMk x y) = y := by
  simp only [prodMk, binaryProductIso_inv_comp_snd_apply]
@[ext]
lemma prod_ext {a : C} (z w : (prod F G).obj a) (h1 : z.1 = w.1) (h2 : z.2 = w.2) :
    z = w := Prod.ext h1 h2
variable (F G)
@[simps]
noncomputable
def binaryProductEquiv (a : C) : (F ⨯ G).obj a ≃ (F.obj a) × (G.obj a) where
  toFun z := ⟨((binaryProductIso F G).hom.app a z).1, ((binaryProductIso F G).hom.app a z).2⟩
  invFun z := prodMk z.1 z.2
  left_inv _ := by simp [prodMk]
  right_inv _ := by simp [prodMk]
@[ext]
lemma prod_ext' (a : C) (z w : (F ⨯ G).obj a)
    (h1 : (Limits.prod.fst (X := F)).app a z = (Limits.prod.fst (X := F)).app a w)
    (h2 : (Limits.prod.snd (X := F)).app a z = (Limits.prod.snd (X := F)).app a w) :
    z = w := by
  apply Equiv.injective (binaryProductEquiv F G a)
  aesop
end prod
section coprod
def coprod : C ⥤ Type w where
  obj a := F.obj a ⊕ G.obj a
  map f x := by
    cases x with
    | inl x => exact .inl (F.map f x)
    | inr x => exact .inr (G.map f x)
variable {F G}
@[simps]
def coprod.inl : F ⟶ coprod F G where
  app _ x := .inl x
@[simps]
def coprod.inr : G ⟶ coprod F G where
  app _ x := .inr x
@[simps]
def coprod.desc {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod F₁ F₂ ⟶ F where
  app a x := by
     cases x with
     | inl x => exact τ₁.app a x
     | inr x => exact τ₂.app a x
  naturality _ _ _ := by
    ext x
    cases x with | _ => simp only [coprod, types_comp_apply, FunctorToTypes.naturality]
@[simp]
lemma coprod.desc_inl {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inl ≫ coprod.desc τ₁ τ₂ = τ₁ := rfl
@[simp]
lemma coprod.desc_inr {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inr ≫ coprod.desc τ₁ τ₂ = τ₂ := rfl
variable (F G)
@[simps!]
def binaryCoproductCocone : BinaryCofan F G :=
  BinaryCofan.mk coprod.inl coprod.inr
@[simps]
def binaryCoproductColimit : IsColimit (binaryCoproductCocone F G) where
  desc (s : BinaryCofan F G) := coprod.desc s.inl s.inr
  fac _ := fun ⟨j⟩ ↦ WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    ext _ x
    cases x with | _ => simp [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
def binaryCoproductColimitCocone : Limits.ColimitCocone (pair F G) :=
  ⟨_, binaryCoproductColimit F G⟩
noncomputable def binaryCoproductIso : F ⨿ G ≅ coprod F G :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone F G)
@[simp]
lemma inl_comp_binaryCoproductIso_hom :
    Limits.coprod.inl ≫ (binaryCoproductIso F G).hom = coprod.inl := by
  simp only [binaryCoproductIso]
  aesop
@[simp]
lemma inl_comp_binaryCoproductIso_hom_apply (a : C) (x : F.obj a) :
    (binaryCoproductIso F G).hom.app a ((Limits.coprod.inl (X := F)).app a x) = .inl x :=
  congr_fun (congr_app (inl_comp_binaryCoproductIso_hom F G) a) x
@[simp]
lemma inr_comp_binaryCoproductIso_hom :
    Limits.coprod.inr ≫ (binaryCoproductIso F G).hom = coprod.inr := by
  simp [binaryCoproductIso]
  aesop
@[simp]
lemma inr_comp_binaryCoproductIso_hom_apply (a : C) (x : G.obj a) :
    (binaryCoproductIso F G).hom.app a ((Limits.coprod.inr (X := F)).app a x) = .inr x :=
  congr_fun (congr_app (inr_comp_binaryCoproductIso_hom F G) a) x
@[simp]
lemma inl_comp_binaryCoproductIso_inv :
    coprod.inl ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inl (X := F)) := rfl
@[simp]
lemma inl_comp_binaryCoproductIso_inv_apply (a : C) (x : F.obj a) :
    (binaryCoproductIso F G).inv.app a (.inl x) = (Limits.coprod.inl (X := F)).app a x := rfl
@[simp]
lemma inr_comp_binaryCoproductIso_inv :
    coprod.inr ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inr (X := F)) := rfl
@[simp]
lemma inr_comp_binaryCoproductIso_inv_apply (a : C) (x : G.obj a) :
    (binaryCoproductIso F G).inv.app a (.inr x) = (Limits.coprod.inr (X := F)).app a x := rfl
variable {F G}
noncomputable
abbrev coprodInl {a : C} (x : F.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inl x)
noncomputable
abbrev coprodInr {a : C} (x : G.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inr x)
variable (F G)
@[simps]
noncomputable
def binaryCoproductEquiv (a : C) :
    (F ⨿ G).obj a ≃ (F.obj a) ⊕ (G.obj a) where
  toFun z := (binaryCoproductIso F G).hom.app a z
  invFun z := (binaryCoproductIso F G).inv.app a z
  left_inv _ := by simp only [hom_inv_id_app_apply]
  right_inv _ := by simp only [inv_hom_id_app_apply]
end coprod
end CategoryTheory.FunctorToTypes