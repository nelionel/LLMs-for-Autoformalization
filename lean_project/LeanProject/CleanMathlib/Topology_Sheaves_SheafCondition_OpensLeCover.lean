import Mathlib.Topology.Sheaves.SheafCondition.Sites
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite
namespace TopCat
variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type w} (U : ι → Opens X)
namespace Presheaf
namespace SheafCondition
def OpensLeCover : Type w :=
  FullSubcategory fun V : Opens X => ∃ i, V ≤ U i
instance : Category (OpensLeCover U) := FullSubcategory.category _
instance [h : Nonempty ι] : Inhabited (OpensLeCover U) :=
  ⟨⟨⊥, let ⟨i⟩ := h; ⟨i, bot_le⟩⟩⟩
namespace OpensLeCover
variable {U}
def index (V : OpensLeCover U) : ι :=
  V.property.choose
def homToIndex (V : OpensLeCover U) : V.obj ⟶ U (index V) :=
  V.property.choose_spec.hom
end OpensLeCover
def opensLeCoverCocone : Cocone (fullSubcategoryInclusion _ : OpensLeCover U ⥤ Opens X) where
  pt := iSup U
  ι := { app := fun V : OpensLeCover U => V.homToIndex ≫ Opens.leSupr U _ }
end SheafCondition
open SheafCondition
def IsSheafOpensLeCover : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (opensLeCoverCocone U).op))
section
variable {Y : Opens X}
@[simps]
def generateEquivalenceOpensLe_functor' (hY : Y = iSup U) :
    (FullSubcategory fun f : Over Y => (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom) ⥤
    OpensLeCover U :=
{ obj := fun f =>
    ⟨f.1.left,
      let ⟨_, h, _, ⟨i, hY⟩, _⟩ := f.2
      ⟨i, hY ▸ h.le⟩⟩
  map := fun {_ _} g => g.left }
@[simps]
def generateEquivalenceOpensLe_inverse' (hY : Y = iSup U) :
    OpensLeCover U ⥤
    (FullSubcategory fun f : Over Y =>
      (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom) where
  obj := fun V => ⟨⟨V.obj, ⟨⟨⟩⟩, homOfLE <| hY ▸ (V.2.choose_spec.trans (le_iSup U (V.2.choose)))⟩,
    ⟨U V.2.choose, V.2.choose_spec.hom, homOfLE <| hY ▸ le_iSup U V.2.choose,
      ⟨V.2.choose, rfl⟩, rfl⟩⟩
  map {_ _} g := Over.homMk g
  map_id _ := by
    refine Over.OverMorphism.ext ?_
    simp only [Functor.id_obj, Sieve.generate_apply, Functor.const_obj_obj, Over.homMk_left,
      eq_iff_true_of_subsingleton]
  map_comp {_ _ _} f g := by
    refine Over.OverMorphism.ext ?_
    simp only [Functor.id_obj, Sieve.generate_apply, Functor.const_obj_obj, Over.homMk_left,
      eq_iff_true_of_subsingleton]
@[simps]
def generateEquivalenceOpensLe (hY : Y = iSup U) :
    (FullSubcategory fun f : Over Y => (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.hom) ≌
    OpensLeCover U where
  functor := generateEquivalenceOpensLe_functor' _ hY
  inverse := generateEquivalenceOpensLe_inverse' _ hY
  unitIso := eqToIso <| CategoryTheory.Functor.ext
    (by rintro ⟨⟨_, _⟩, _⟩; dsimp; congr)
    (by intros; refine Over.OverMorphism.ext ?_; aesop_cat)
  counitIso := eqToIso <| CategoryTheory.Functor.hext
    (by intro; refine FullSubcategory.ext ?_; rfl) (by intros; rfl)
@[simps]
def whiskerIsoMapGenerateCocone (hY : Y = iSup U) :
    (F.mapCone (opensLeCoverCocone U).op).whisker (generateEquivalenceOpensLe U hY).op.functor ≅
      F.mapCone (Sieve.generate (presieveOfCoveringAux U Y)).arrows.cocone.op where
  hom :=
    { hom := F.map (eqToHom (congr_arg op hY.symm))
      w := fun j => by
        erw [← F.map_comp]
        dsimp
        congr 1 }
  inv :=
    { hom := F.map (eqToHom (congr_arg op hY))
      w := fun j => by
        erw [← F.map_comp]
        dsimp
        congr 1 }
  hom_inv_id := by
    ext
    simp [eqToHom_map]
  inv_hom_id := by
    ext
    simp [eqToHom_map]
def isLimitOpensLeEquivGenerate₁ (hY : Y = iSup U) :
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
      IsLimit (F.mapCone (Sieve.generate (presieveOfCoveringAux U Y)).arrows.cocone.op) :=
  (IsLimit.whiskerEquivalenceEquiv (generateEquivalenceOpensLe U hY).op).trans
    (IsLimit.equivIsoLimit (whiskerIsoMapGenerateCocone F U hY))
def isLimitOpensLeEquivGenerate₂ (R : Presieve Y)
    (hR : Sieve.generate R ∈ Opens.grothendieckTopology X Y) :
    IsLimit (F.mapCone (opensLeCoverCocone (coveringOfPresieve Y R)).op) ≃
      IsLimit (F.mapCone (Sieve.generate R).arrows.cocone.op) := by
  convert isLimitOpensLeEquivGenerate₁ F (coveringOfPresieve Y R)
      (coveringOfPresieve.iSup_eq_of_mem_grothendieck Y R hR).symm using 1
  rw [covering_presieve_eq_self R]
theorem isSheaf_iff_isSheafOpensLeCover : F.IsSheaf ↔ F.IsSheafOpensLeCover := by
  refine (Presheaf.isSheaf_iff_isLimit _ _).trans ?_
  constructor
  · intro h ι U
    rw [(isLimitOpensLeEquivGenerate₁ F U rfl).nonempty_congr]
    apply h
    apply presieveOfCovering.mem_grothendieckTopology
  · intro h Y S
    rw [← Sieve.generate_sieve S]
    intro hS
    rw [← (isLimitOpensLeEquivGenerate₂ F S.1 hS).nonempty_congr]
    apply h
end
end Presheaf
end TopCat