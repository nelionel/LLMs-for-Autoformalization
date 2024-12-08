import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.CommSq
universe v v' u u'
namespace CategoryTheory
open Category
variable (C : Type u) [Category.{v} C] {D : Type u'} [Category.{v'} D]
structure Square where
  {X₁ : C}
  {X₂ : C}
  {X₃ : C}
  {X₄ : C}
  f₁₂ : X₁ ⟶ X₂
  f₁₃ : X₁ ⟶ X₃
  f₂₄ : X₂ ⟶ X₄
  f₃₄ : X₃ ⟶ X₄
  fac : f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄
namespace Square
variable {C}
lemma commSq (sq : Square C) : CommSq sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄ where
  w := sq.fac
@[ext]
structure Hom (sq₁ sq₂ : Square C) where
  τ₁ : sq₁.X₁ ⟶ sq₂.X₁
  τ₂ : sq₁.X₂ ⟶ sq₂.X₂
  τ₃ : sq₁.X₃ ⟶ sq₂.X₃
  τ₄ : sq₁.X₄ ⟶ sq₂.X₄
  comm₁₂ : sq₁.f₁₂ ≫ τ₂ = τ₁ ≫ sq₂.f₁₂ := by aesop_cat
  comm₁₃ : sq₁.f₁₃ ≫ τ₃ = τ₁ ≫ sq₂.f₁₃ := by aesop_cat
  comm₂₄ : sq₁.f₂₄ ≫ τ₄ = τ₂ ≫ sq₂.f₂₄ := by aesop_cat
  comm₃₄ : sq₁.f₃₄ ≫ τ₄ = τ₃ ≫ sq₂.f₃₄ := by aesop_cat
namespace Hom
attribute [reassoc (attr := simp)] comm₁₂ comm₁₃ comm₂₄ comm₃₄
@[simps]
def id (sq : Square C) : Hom sq sq where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _
@[simps]
def comp {sq₁ sq₂ sq₃ : Square C} (f : Hom sq₁ sq₂) (g : Hom sq₂ sq₃) : Hom sq₁ sq₃ where
  τ₁ := f.τ₁ ≫ g.τ₁
  τ₂ := f.τ₂ ≫ g.τ₂
  τ₃ := f.τ₃ ≫ g.τ₃
  τ₄ := f.τ₄ ≫ g.τ₄
end Hom
@[simps!]
instance category : Category (Square C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
@[ext]
lemma hom_ext {sq₁ sq₂ : Square C} {f g : sq₁ ⟶ sq₂}
    (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂)
    (h₃ : f.τ₃ = g.τ₃) (h₄ : f.τ₄ = g.τ₄) : f = g :=
  Hom.ext h₁ h₂ h₃ h₄
def isoMk {sq₁ sq₂ : Square C} (e₁ : sq₁.X₁ ≅ sq₂.X₁) (e₂ : sq₁.X₂ ≅ sq₂.X₂)
    (e₃ : sq₁.X₃ ≅ sq₂.X₃) (e₄ : sq₁.X₄ ≅ sq₂.X₄)
    (comm₁₂ : sq₁.f₁₂ ≫ e₂.hom = e₁.hom ≫ sq₂.f₁₂)
    (comm₁₃ : sq₁.f₁₃ ≫ e₃.hom = e₁.hom ≫ sq₂.f₁₃)
    (comm₂₄ : sq₁.f₂₄ ≫ e₄.hom = e₂.hom ≫ sq₂.f₂₄)
    (comm₃₄ : sq₁.f₃₄ ≫ e₄.hom = e₃.hom ≫ sq₂.f₃₄) :
    sq₁ ≅ sq₂ where
  hom :=
    { τ₁ := e₁.hom
      τ₂ := e₂.hom
      τ₃ := e₃.hom
      τ₄ := e₄.hom }
  inv :=
    { τ₁ := e₁.inv
      τ₂ := e₂.inv
      τ₃ := e₃.inv
      τ₄ := e₄.inv
      comm₁₂ := by simp only [← cancel_mono e₂.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₂, Iso.inv_hom_id_assoc]
      comm₁₃ := by simp only [← cancel_mono e₃.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₃, Iso.inv_hom_id_assoc]
      comm₂₄ := by simp only [← cancel_mono e₄.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₂₄, Iso.inv_hom_id_assoc]
      comm₃₄ := by simp only [← cancel_mono e₄.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₃₄, Iso.inv_hom_id_assoc] }
@[simps]
def flip (sq : Square C) : Square C where
  fac := sq.fac.symm
@[simps]
def flipFunctor : Square C ⥤ Square C where
  obj := flip
  map φ :=
    { τ₁ := φ.τ₁
      τ₂ := φ.τ₃
      τ₃ := φ.τ₂
      τ₄ := φ.τ₄ }
@[simps]
def flipEquivalence : Square C ≌ Square C where
  functor := flipFunctor
  inverse := flipFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _
@[simps!]
def toArrowArrowFunctor : Square C ⥤ Arrow (Arrow C) where
  obj sq := Arrow.mk (Arrow.homMk sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)
  map φ := Arrow.homMk (u := Arrow.homMk φ.comm₁₃.symm)
    (v := Arrow.homMk φ.comm₂₄.symm) (by aesop_cat)
@[simps!]
def fromArrowArrowFunctor : Arrow (Arrow C) ⥤ Square C where
  obj f := { fac := f.hom.w }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.right.left
      τ₃ := φ.left.right
      τ₄ := φ.right.right
      comm₁₂ := Arrow.leftFunc.congr_map φ.w.symm
      comm₁₃ := φ.left.w.symm
      comm₂₄ := φ.right.w.symm
      comm₃₄ := Arrow.rightFunc.congr_map φ.w.symm }
@[simps]
def arrowArrowEquivalence : Square C ≌ Arrow (Arrow C) where
  functor := toArrowArrowFunctor
  inverse := fromArrowArrowFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _
@[simps!]
def toArrowArrowFunctor' : Square C ⥤ Arrow (Arrow C) where
  obj sq := Arrow.mk (Arrow.homMk sq.fac.symm : Arrow.mk sq.f₁₂ ⟶ Arrow.mk sq.f₃₄)
  map φ := Arrow.homMk (u := Arrow.homMk φ.comm₁₂.symm)
    (v := Arrow.homMk φ.comm₃₄.symm) (by aesop_cat)
@[simps!]
def fromArrowArrowFunctor' : Arrow (Arrow C) ⥤ Square C where
  obj f := { fac := f.hom.w.symm }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.left.right
      τ₃ := φ.right.left
      τ₄ := φ.right.right
      comm₁₂ := φ.left.w.symm
      comm₁₃ := Arrow.leftFunc.congr_map φ.w.symm
      comm₂₄ := Arrow.rightFunc.congr_map φ.w.symm
      comm₃₄ := φ.right.w.symm }
@[simps]
def arrowArrowEquivalence' : Square C ≌ Arrow (Arrow C) where
  functor := toArrowArrowFunctor'
  inverse := fromArrowArrowFunctor'
  unitIso := Iso.refl _
  counitIso := Iso.refl _
@[simps]
def evaluation₁ : Square C ⥤ C where
  obj sq := sq.X₁
  map φ := φ.τ₁
@[simps]
def evaluation₂ : Square C ⥤ C where
  obj sq := sq.X₂
  map φ := φ.τ₂
@[simps]
def evaluation₃ : Square C ⥤ C where
  obj sq := sq.X₃
  map φ := φ.τ₃
@[simps]
def evaluation₄ : Square C ⥤ C where
  obj sq := sq.X₄
  map φ := φ.τ₄
@[simps]
protected def op (sq : Square C) : Square Cᵒᵖ where
  f₁₂ := sq.f₂₄.op
  f₁₃ := sq.f₃₄.op
  f₂₄ := sq.f₁₂.op
  f₃₄ := sq.f₁₃.op
  fac := Quiver.Hom.unop_inj sq.fac
@[simps]
protected def unop (sq : Square Cᵒᵖ) : Square C where
  f₁₂ := sq.f₂₄.unop
  f₁₃ := sq.f₃₄.unop
  f₂₄ := sq.f₁₂.unop
  f₃₄ := sq.f₁₃.unop
  fac := Quiver.Hom.op_inj sq.fac
@[simps]
def opFunctor : (Square C)ᵒᵖ ⥤ Square Cᵒᵖ where
  obj sq := sq.unop.op
  map φ :=
    { τ₁ := φ.unop.τ₄.op
      τ₂ := φ.unop.τ₂.op
      τ₃ := φ.unop.τ₃.op
      τ₄ := φ.unop.τ₁.op
      comm₁₂ := Quiver.Hom.unop_inj (by simp)
      comm₁₃ := Quiver.Hom.unop_inj (by simp)
      comm₂₄ := Quiver.Hom.unop_inj (by simp)
      comm₃₄ := Quiver.Hom.unop_inj (by simp) }
def unopFunctor : (Square Cᵒᵖ)ᵒᵖ ⥤ Square C where
  obj sq := sq.unop.unop
  map φ :=
    { τ₁ := φ.unop.τ₄.unop
      τ₂ := φ.unop.τ₂.unop
      τ₃ := φ.unop.τ₃.unop
      τ₄ := φ.unop.τ₁.unop
      comm₁₂ := Quiver.Hom.op_inj (by simp)
      comm₁₃ := Quiver.Hom.op_inj (by simp)
      comm₂₄ := Quiver.Hom.op_inj (by simp)
      comm₃₄ := Quiver.Hom.op_inj (by simp) }
def opEquivalence : (Square C)ᵒᵖ ≌ Square Cᵒᵖ where
  functor := opFunctor
  inverse := unopFunctor.rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _
@[simps]
def map (sq : Square C) (F : C ⥤ D) : Square D where
  f₁₂ := F.map sq.f₁₂
  f₁₃ := F.map sq.f₁₃
  f₂₄ := F.map sq.f₂₄
  f₃₄ := F.map sq.f₃₄
  fac := by simpa using F.congr_map sq.fac
end Square
variable {C}
namespace Functor
@[simps]
def mapSquare (F : C ⥤ D) : Square C ⥤ Square D where
  obj sq := sq.map F
  map φ :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      τ₄ := F.map φ.τ₄
      comm₁₂ := by simpa only [Functor.map_comp] using F.congr_map φ.comm₁₂
      comm₁₃ := by simpa only [Functor.map_comp] using F.congr_map φ.comm₁₃
      comm₂₄ := by simpa only [Functor.map_comp] using F.congr_map φ.comm₂₄
      comm₃₄ := by simpa only [Functor.map_comp] using F.congr_map φ.comm₃₄ }
end Functor
@[simps]
def NatTrans.mapSquare {F G : C ⥤ D} (τ : F ⟶ G) :
    F.mapSquare ⟶ G.mapSquare where
  app sq :=
    { τ₁ := τ.app _
      τ₂ := τ.app _
      τ₃ := τ.app _
      τ₄ := τ.app _ }
@[simps]
def Square.mapFunctor : (C ⥤ D) ⥤ Square C ⥤ Square D where
  obj F := F.mapSquare
  map τ := NatTrans.mapSquare τ
end CategoryTheory