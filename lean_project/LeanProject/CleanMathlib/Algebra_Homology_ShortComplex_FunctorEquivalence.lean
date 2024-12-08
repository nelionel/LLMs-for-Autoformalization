import Mathlib.Algebra.Homology.ShortComplex.Basic
namespace CategoryTheory
open Limits
variable (J C : Type*) [Category J] [Category C] [HasZeroMorphisms C]
namespace ShortComplex
namespace FunctorEquivalence
attribute [local simp] ShortComplex.Hom.comm₁₂ ShortComplex.Hom.comm₂₃
@[simps]
def functor : ShortComplex (J ⥤ C) ⥤ J ⥤ ShortComplex C where
  obj S :=
    { obj := fun j => S.map ((evaluation J C).obj j)
      map := fun f => S.mapNatTrans ((evaluation J C).map f) }
  map φ :=
    { app := fun j => ((evaluation J C).obj j).mapShortComplex.map φ }
@[simps]
def inverse : (J ⥤ ShortComplex C) ⥤ ShortComplex (J ⥤ C) where
  obj F :=
    { f := whiskerLeft F π₁Toπ₂
      g := whiskerLeft F π₂Toπ₃
      zero := by aesop_cat }
  map φ := Hom.mk (whiskerRight φ π₁) (whiskerRight φ π₂) (whiskerRight φ π₃)
    (by aesop_cat) (by aesop_cat)
@[simps!]
def unitIso : 𝟭 _ ≅ functor J C ⋙ inverse J C :=
  NatIso.ofComponents (fun _ => isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat))
    (by aesop_cat) (by aesop_cat)) (by aesop_cat)
@[simps!]
def counitIso : inverse J C ⋙ functor J C ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by aesop_cat) (by aesop_cat)) (by aesop_cat)) (by aesop_cat)
end FunctorEquivalence
@[simps]
def functorEquivalence : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C where
  functor := FunctorEquivalence.functor J C
  inverse := FunctorEquivalence.inverse J C
  unitIso := FunctorEquivalence.unitIso J C
  counitIso := FunctorEquivalence.counitIso J C
end ShortComplex
end CategoryTheory