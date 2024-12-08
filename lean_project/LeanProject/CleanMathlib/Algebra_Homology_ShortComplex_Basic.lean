import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
namespace CategoryTheory
open Category Limits
variable (C D : Type*) [Category C] [Category D]
structure ShortComplex [HasZeroMorphisms C] where
  {X₁ : C}
  {X₂ : C}
  {X₃ : C}
  f : X₁ ⟶ X₂
  g : X₂ ⟶ X₃
  zero : f ≫ g = 0
namespace ShortComplex
attribute [reassoc (attr := simp)] ShortComplex.zero
variable {C}
variable [HasZeroMorphisms C]
@[ext]
structure Hom (S₁ S₂ : ShortComplex C) where
  τ₁ : S₁.X₁ ⟶ S₂.X₁
  τ₂ : S₁.X₂ ⟶ S₂.X₂
  τ₃ : S₁.X₃ ⟶ S₂.X₃
  comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by aesop_cat
  comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by aesop_cat
attribute [reassoc] Hom.comm₁₂ Hom.comm₂₃
attribute [local simp] Hom.comm₁₂ Hom.comm₂₃ Hom.comm₁₂_assoc Hom.comm₂₃_assoc
variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}
@[simps]
def Hom.id : Hom S S where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
@[simps]
def Hom.comp (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃) : Hom S₁ S₃ where
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃
instance : Category (ShortComplex C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
@[ext]
lemma hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g :=
  Hom.ext h₁ h₂ h₃
@[simps]
def homMk {S₁ S₂ : ShortComplex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
    (τ₃ : S₁.X₃ ⟶ S₂.X₃) (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
    (comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃) : S₁ ⟶ S₂ := ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩
@[simp] lemma id_τ₁ : Hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ : Hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ : Hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
@[reassoc] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
@[reassoc] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
@[reassoc] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl
attribute [simp] comp_τ₁ comp_τ₂ comp_τ₃
instance : Zero (S₁ ⟶ S₂) := ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0 }⟩
variable (S₁ S₂)
@[simp] lemma zero_τ₁ : Hom.τ₁ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₂ : Hom.τ₂ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₃ : Hom.τ₃ (0 : S₁ ⟶ S₂) = 0 := rfl
variable {S₁ S₂}
instance : HasZeroMorphisms (ShortComplex C) where
@[simps]
def π₁ : ShortComplex C ⥤ C where
  obj S := S.X₁
  map f := f.τ₁
@[simps]
def π₂ : ShortComplex C ⥤ C where
  obj S := S.X₂
  map f := f.τ₂
@[simps]
def π₃ : ShortComplex C ⥤ C where
  obj S := S.X₃
  map f := f.τ₃
instance preservesZeroMorphisms_π₁ : Functor.PreservesZeroMorphisms (π₁ : _ ⥤ C) where
instance preservesZeroMorphisms_π₂ : Functor.PreservesZeroMorphisms (π₂ : _ ⥤ C) where
instance preservesZeroMorphisms_π₃ : Functor.PreservesZeroMorphisms (π₃ : _ ⥤ C) where
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₁ := (inferInstance : IsIso (π₁.mapIso (asIso f)).hom)
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₂ := (inferInstance : IsIso (π₂.mapIso (asIso f)).hom)
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₃ := (inferInstance : IsIso (π₃.mapIso (asIso f)).hom)
@[simps] def π₁Toπ₂ : (π₁ : _ ⥤ C) ⟶ π₂ where
  app S := S.f
@[simps] def π₂Toπ₃ : (π₂ : _ ⥤ C) ⟶ π₃ where
  app S := S.g
@[reassoc (attr := simp)]
lemma π₁Toπ₂_comp_π₂Toπ₃ : (π₁Toπ₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂Toπ₃ = 0 := by aesop_cat
variable {D}
variable [HasZeroMorphisms D]
@[simps]
def map (F : C ⥤ D) [F.PreservesZeroMorphisms] : ShortComplex D :=
  ShortComplex.mk (F.map S.f) (F.map S.g) (by rw [← F.map_comp, S.zero, F.map_zero])
@[simps]
def mapNatTrans {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G) :
    S.map F ⟶ S.map G where
  τ₁ := τ.app _
  τ₂ := τ.app _
  τ₃ := τ.app _
@[simps]
def mapNatIso {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ≅ G) :
    S.map F ≅ S.map G where
  hom := S.mapNatTrans τ.hom
  inv := S.mapNatTrans τ.inv
@[simps]
def _root_.CategoryTheory.Functor.mapShortComplex (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    ShortComplex C ⥤ ShortComplex D where
  obj S := S.map F
  map φ :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      comm₁₂ := by
        dsimp
        simp only [← F.map_comp, φ.comm₁₂]
      comm₂₃ := by
        dsimp
        simp only [← F.map_comp, φ.comm₂₃] }
@[simps]
def isoMk (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃)
    (comm₁₂ : e₁.hom ≫ S₂.f = S₁.f ≫ e₂.hom := by aesop_cat)
    (comm₂₃ : e₂.hom ≫ S₂.g = S₁.g ≫ e₃.hom := by aesop_cat) :
    S₁ ≅ S₂ where
  hom := ⟨e₁.hom, e₂.hom, e₃.hom, comm₁₂, comm₂₃⟩
  inv := homMk e₁.inv e₂.inv e₃.inv
    (by rw [← cancel_mono e₂.hom, assoc, assoc, e₂.inv_hom_id, comp_id,
          ← comm₁₂, e₁.inv_hom_id_assoc])
    (by rw [← cancel_mono e₃.hom, assoc, assoc, e₃.inv_hom_id, comp_id,
          ← comm₂₃, e₂.inv_hom_id_assoc])
lemma isIso_of_isIso (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIso f :=
  (isoMk (asIso f.τ₁) (asIso f.τ₂) (asIso f.τ₃)).isIso_hom
@[simps]
def op : ShortComplex Cᵒᵖ :=
  mk S.g.op S.f.op (by simp only [← op_comp, S.zero]; rfl)
@[simps]
def opMap (φ : S₁ ⟶ S₂) : S₂.op ⟶ S₁.op where
  τ₁ := φ.τ₃.op
  τ₂ := φ.τ₂.op
  τ₃ := φ.τ₁.op
  comm₁₂ := by
    dsimp
    simp only [← op_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← op_comp, φ.comm₁₂]
@[simp]
lemma opMap_id : opMap (𝟙 S) = 𝟙 S.op := rfl
@[simps]
def unop (S : ShortComplex Cᵒᵖ) : ShortComplex C :=
  mk S.g.unop S.f.unop (by simp only [← unop_comp, S.zero]; rfl)
@[simps]
def unopMap {S₁ S₂ : ShortComplex Cᵒᵖ} (φ : S₁ ⟶ S₂) : S₂.unop ⟶ S₁.unop where
  τ₁ := φ.τ₃.unop
  τ₂ := φ.τ₂.unop
  τ₃ := φ.τ₁.unop
  comm₁₂ := by
    dsimp
    simp only [← unop_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← unop_comp, φ.comm₁₂]
@[simp]
lemma unopMap_id (S : ShortComplex Cᵒᵖ) : unopMap (𝟙 S) = 𝟙 S.unop := rfl
variable (C)
@[simps]
def opFunctor : (ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ where
  obj S := (Opposite.unop S).op
  map φ := opMap φ.unop
@[simps]
def unopFunctor : ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ where
  obj S := Opposite.op (S.unop)
  map φ := (unopMap φ).op
@[simps]
def opEquiv : (ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ where
  functor := opFunctor C
  inverse := unopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
variable {C}
abbrev unopOp (S : ShortComplex Cᵒᵖ) : S.unop.op ≅ S := (opEquiv C).counitIso.app S
abbrev opUnop (S : ShortComplex C) : S.op.unop ≅ S :=
  Iso.unop ((opEquiv C).unitIso.app (Opposite.op S))
end ShortComplex
end CategoryTheory