import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Noetherian.Defs
open Opposite
open CategoryTheory
open CategoryTheory.Limits
noncomputable section
universe u v v'
namespace localCohomology
section
variable {R : Type u} [CommRing R] {D : Type v} [SmallCategory D]
def ringModIdeals (I : D ⥤ Ideal R) : D ⥤ ModuleCat.{u} R where
  obj t := ModuleCat.of R <| R ⧸ I.obj t
  map w := Submodule.mapQ _ _ LinearMap.id (I.map w).down.down
  map_comp f g := by apply Submodule.linearMap_qext; rfl
instance moduleCat_enoughProjectives' : EnoughProjectives (ModuleCat.{u} R) :=
  ModuleCat.moduleCat_enoughProjectives.{u}
def diagram (I : D ⥤ Ideal R) (i : ℕ) : Dᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i
end
section
variable {R : Type max u v} [CommRing R] {D : Type v} [SmallCategory D]
lemma hasColimitDiagram (I : D ⥤ Ideal R) (i : ℕ) :
    HasColimit (diagram I i) := by
  have : HasColimitsOfShape Dᵒᵖ (AddCommGrpMax.{u, v}) := inferInstance
  infer_instance
def ofDiagram (I : D ⥤ Ideal R) (i : ℕ) : ModuleCatMax.{u, v} R ⥤ ModuleCatMax.{u, v} R :=
  have := hasColimitDiagram.{u, v} I i
  colimit (diagram I i)
end
section
variable {R : Type max u v v'} [CommRing R] {D : Type v} [SmallCategory D]
variable {E : Type v'} [SmallCategory E] (I' : E ⥤ D) (I : D ⥤ Ideal R)
def diagramComp (i : ℕ) : diagram (I' ⋙ I) i ≅ I'.op ⋙ diagram I i :=
  Iso.refl _
@[nolint unusedHavesSuffices]
def isoOfFinal [Functor.Initial I'] (i : ℕ) :
    ofDiagram.{max u v, v'} (I' ⋙ I) i ≅ ofDiagram.{max u v', v} I i :=
  have := hasColimitDiagram.{max u v', v} I i
  have := hasColimitDiagram.{max u v, v'} (I' ⋙ I) i
  HasColimit.isoOfNatIso (diagramComp.{u} I' I i) ≪≫ Functor.Final.colimitIso _ _
end
section Diagrams
variable {R : Type u} [CommRing R]
def idealPowersDiagram (J : Ideal R) : ℕᵒᵖ ⥤ Ideal R where
  obj t := J ^ unop t
  map w := ⟨⟨Ideal.pow_le_pow_right w.unop.down.down⟩⟩
def SelfLERadical (J : Ideal R) : Type u :=
  FullSubcategory fun J' : Ideal R => J ≤ J'.radical
instance (J : Ideal R) : Category (SelfLERadical J) :=
  (FullSubcategory.category _)
instance SelfLERadical.inhabited (J : Ideal R) : Inhabited (SelfLERadical J) where
  default := ⟨J, Ideal.le_radical⟩
def selfLERadicalDiagram (J : Ideal R) : SelfLERadical J ⥤ Ideal R :=
  fullSubcategoryInclusion _
end Diagrams
end localCohomology
section ModelsForLocalCohomology
open localCohomology
variable {R : Type u} [CommRing R]
def localCohomology (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram (idealPowersDiagram J) i
def localCohomology.ofSelfLERadical (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram.{u} (selfLERadicalDiagram.{u} J) i
end ModelsForLocalCohomology
namespace localCohomology
section LocalCohomologyEquiv
variable {R : Type u} [CommRing R]
def idealPowersToSelfLERadical (J : Ideal R) : ℕᵒᵖ ⥤ SelfLERadical J :=
  FullSubcategory.lift _ (idealPowersDiagram J) fun k => by
    change _ ≤ (J ^ unop k).radical
    cases' unop k with n
    · simp [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top]
    · simp only [J.radical_pow n.succ_ne_zero, Ideal.le_radical]
variable {I J K : Ideal R}
instance ideal_powers_initial [hR : IsNoetherian R R] :
    Functor.Initial (idealPowersToSelfLERadical J) where
  out J' := by
    apply (config := {allowSynthFailures := true }) zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J'.2 (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk (⟨⟨hk⟩⟩ : (idealPowersToSelfLERadical J).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
example : HasColimitsOfSize.{0, 0, u, u + 1} (ModuleCat.{u, u} R) := inferInstance
def isoSelfLERadical (J : Ideal.{u} R) [IsNoetherian.{u,u} R R] (i : ℕ) :
    localCohomology.ofSelfLERadical.{u} J i ≅ localCohomology.{u} J i :=
  (localCohomology.isoOfFinal.{u, u, 0} (idealPowersToSelfLERadical.{u} J)
    (selfLERadicalDiagram.{u} J) i).symm ≪≫
      HasColimit.isoOfNatIso.{0,0,u+1,u+1} (Iso.refl.{u+1,u+1} _)
def SelfLERadical.cast (hJK : J.radical = K.radical) : SelfLERadical J ⥤ SelfLERadical K :=
  FullSubcategory.map fun L hL => by
    rw [← Ideal.radical_le_radical_iff] at hL ⊢
    exact hJK.symm.trans_le hL
def SelfLERadical.castEquivalence (hJK : J.radical = K.radical) :
    SelfLERadical J ≌ SelfLERadical K where
  functor := SelfLERadical.cast hJK
  inverse := SelfLERadical.cast hJK.symm
  unitIso := Iso.refl _
  counitIso := Iso.refl _
instance SelfLERadical.cast_isEquivalence (hJK : J.radical = K.radical) :
    (SelfLERadical.cast hJK).IsEquivalence :=
  (castEquivalence hJK).isEquivalence_functor
def SelfLERadical.isoOfSameRadical (hJK : J.radical = K.radical) (i : ℕ) :
    ofSelfLERadical J i ≅ ofSelfLERadical K i :=
  (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm
def isoOfSameRadical [IsNoetherian R R] (hJK : J.radical = K.radical) (i : ℕ) :
    localCohomology J i ≅ localCohomology K i :=
  (isoSelfLERadical J i).symm ≪≫ SelfLERadical.isoOfSameRadical hJK i ≪≫ isoSelfLERadical K i
end LocalCohomologyEquiv
end localCohomology