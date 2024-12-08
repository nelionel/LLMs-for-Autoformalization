import Mathlib.AlgebraicTopology.DoldKan.PInfty
open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
noncomputable section
namespace AlgebraicTopology
namespace DoldKan
variable {C : Type*} [Category C] [Preadditive C]
@[simps]
def N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ) where
  obj X :=
    { X := AlternatingFaceMapComplex.obj X
      p := PInfty
      idem := PInfty_idem }
  map f :=
    { f := PInfty ≫ AlternatingFaceMapComplex.map f }
@[simps!]
def N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  (functorExtension₁ _ _).obj N₁
def toKaroubiCompN₂IsoN₁ : toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁ :=
  (functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app N₁
@[simp]
lemma toKaroubiCompN₂IsoN₁_hom_app (X : SimplicialObject C) :
    (toKaroubiCompN₂IsoN₁.hom.app X).f = PInfty := rfl
@[simp]
lemma toKaroubiCompN₂IsoN₁_inv_app (X : SimplicialObject C) :
    (toKaroubiCompN₂IsoN₁.inv.app X).f = PInfty := rfl
end DoldKan
end AlgebraicTopology