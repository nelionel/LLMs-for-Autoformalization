import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Triangulated.Basic
noncomputable section
open CategoryTheory
open CategoryTheory.Preadditive
open CategoryTheory.Limits
universe v v₀ v₁ v₂ u u₀ u₁ u₂
namespace CategoryTheory.Pretriangulated
open CategoryTheory.Category
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasShift C ℤ]
variable (X : C)
@[simps!]
def Triangle.rotate (T : Triangle C) : Triangle C :=
  Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')
section
@[simps!]
def Triangle.invRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (-T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftEquiv C (1 : ℤ)).unitIso.inv.app _) (T.mor₁)
    (T.mor₂ ≫ (shiftEquiv C (1 : ℤ)).counitIso.inv.app _ )
end
attribute [local simp] shift_shift_neg' shift_neg_shift'
  shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app
  shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app
variable (C)
@[simps]
def rotate : Triangle C ⥤ Triangle C where
  obj := Triangle.rotate
  map f :=
  { hom₁ := f.hom₂
    hom₂ := f.hom₃
    hom₃ := f.hom₁⟦1⟧'
    comm₃ := by
      dsimp
      simp only [comp_neg, neg_comp, ← Functor.map_comp, f.comm₁] }
@[simps]
def invRotate : Triangle C ⥤ Triangle C where
  obj := Triangle.invRotate
  map f :=
  { hom₁ := f.hom₃⟦-1⟧'
    hom₂ := f.hom₁
    hom₃ := f.hom₂
    comm₁ := by
      dsimp
      simp only [neg_comp, assoc, comp_neg, neg_inj, ← Functor.map_comp_assoc, ← f.comm₃]
      rw [Functor.map_comp, assoc]
      erw [← NatTrans.naturality]
      rfl
    comm₃ := by
      erw [← reassoc_of% f.comm₂, Category.assoc, ← NatTrans.naturality]
      rfl }
variable {C}
variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
@[simps!]
def rotCompInvRot : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _
    ((shiftEquiv C (1 : ℤ)).unitIso.app T.obj₁) (Iso.refl _) (Iso.refl _)
@[simps!]
def invRotCompRot : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C) :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftEquiv C (1 : ℤ)).counitIso.app T.obj₃)
variable (C)
@[simps]
def triangleRotation : Equivalence (Triangle C) (Triangle C) where
  functor := rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot
variable {C}
instance : (rotate C).IsEquivalence := by
  change (triangleRotation C).functor.IsEquivalence
  infer_instance
instance : (invRotate C).IsEquivalence := by
  change (triangleRotation C).inverse.IsEquivalence
  infer_instance
end CategoryTheory.Pretriangulated