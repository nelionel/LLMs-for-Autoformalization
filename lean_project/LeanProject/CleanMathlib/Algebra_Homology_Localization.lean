import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Localization.Composition
import Mathlib.CategoryTheory.Localization.HasLocalization
open CategoryTheory Limits
section
variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C]
lemma HomologicalComplex.homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => by
  rw [mem_quasiIso_iff] at hf
  dsimp
  infer_instance
variable [(HomologicalComplex.quasiIso C c).HasLocalization]
abbrev HomologicalComplexUpToQuasiIso := (HomologicalComplex.quasiIso C c).Localization'
variable {C c} in
abbrev HomologicalComplexUpToQuasiIso.Q :
    HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  (HomologicalComplex.quasiIso C c).Q'
namespace HomologicalComplexUpToQuasiIso
noncomputable def homologyFunctor (i : ι) : HomologicalComplexUpToQuasiIso C c ⥤ C :=
  Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q
noncomputable def homologyFunctorFactors (i : ι) :
    Q ⋙ homologyFunctor C c i ≅ HomologicalComplex.homologyFunctor C c i :=
  Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q
variable {C c}
lemma isIso_Q_map_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.quasiIso C c f := by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 ?_
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h
end HomologicalComplexUpToQuasiIso
end
section
variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]
lemma HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences
    [(HomologicalComplex.quasiIso C c).HasLocalization] :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQuasiIso.Q :=
  MorphismProperty.IsInvertedBy.of_le _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_le_quasiIso C c)
namespace HomotopyCategory
def quasiIso : MorphismProperty (HomotopyCategory C c) :=
  fun _ _ f => ∀ (i : ι), IsIso ((homologyFunctor C c i).map f)
variable {C c}
lemma mem_quasiIso_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) :
    quasiIso C c f ↔ ∀ (n : ι), IsIso ((homologyFunctor _ _ n).map f) := by
  rfl
lemma quotient_map_mem_quasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    quasiIso C c ((quotient C c).map f) ↔ HomologicalComplex.quasiIso C c f := by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]
variable (C c)
instance respectsIso_quasiIso : (quasiIso C c).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)
lemma homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i
lemma quasiIso_eq_quasiIso_map_quotient :
    quasiIso C c = (HomologicalComplex.quasiIso C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_quasiIso_iff] at h
    exact ((quasiIso C c).arrow_mk_iso_iff e).1 h
end HomotopyCategory
class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category C] [Preadditive C]
    [CategoryWithHomology C] : Prop where
  areEqualizedByLocalization {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    AreEqualizedByLocalization (HomologicalComplex.quasiIso C c) f g
namespace HomologicalComplexUpToQuasiIso
variable {C c}
variable [(HomologicalComplex.quasiIso C c).HasLocalization] [c.QFactorsThroughHomotopy C]
lemma Q_map_eq_of_homotopy {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    Q.map f = Q.map g :=
  (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q
def Qh : HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  CategoryTheory.Quotient.lift _ HomologicalComplexUpToQuasiIso.Q (by
    intro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)
variable (C c)
def quotientCompQhIso : HomotopyCategory.quotient C c ⋙ Qh ≅ Q := by
  apply Quotient.lift.isLift
lemma Qh_inverts_quasiIso : (HomotopyCategory.quasiIso C c).IsInvertedBy Qh := by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff φ,
    ← HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2
instance : (HomotopyCategory.quotient C c ⋙ Qh).IsLocalization
    (HomologicalComplex.quasiIso C c) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm
noncomputable def homologyFunctorFactorsh (i : ι ) :
    Qh ⋙ homologyFunctor C c i ≅ HomotopyCategory.homologyFunctor C c i :=
  Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i  ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)
section
variable [(HomotopyCategory.quotient C c).IsLocalization
  (HomologicalComplex.homotopyEquivalences C c)]
instance : HomologicalComplexUpToQuasiIso.Qh.IsLocalization (HomotopyCategory.quasiIso C c) :=
  Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
    Qh (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quasiIso C c) (HomologicalComplex.quasiIso C c)
    (homotopyEquivalences_le_quasiIso C c)
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient C c)
end
end HomologicalComplexUpToQuasiIso
end
section Cylinder
variable {ι : Type*} (c : ComplexShape ι) (hc : ∀ j, ∃ i, c.Rel i j)
  (C : Type*) [Category C] [Preadditive C] [HasBinaryBiproducts C]
include hc
def ComplexShape.strictUniversalPropertyFixedTargetQuotient (E : Type*) [Category E] :
    Localization.StrictUniversalPropertyFixedTarget (HomotopyCategory.quotient C c)
      (HomologicalComplex.homotopyEquivalences C c) E where
  inverts := HomotopyCategory.quotient_inverts_homotopyEquivalences C c
  lift F hF := CategoryTheory.Quotient.lift _ F (by
    intro K L f g ⟨h⟩
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc F hF)
  fac _ _ := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h
lemma ComplexShape.quotient_isLocalization :
    (HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences _ _) := by
  apply Functor.IsLocalization.mk'
  all_goals apply c.strictUniversalPropertyFixedTargetQuotient hc
lemma ComplexShape.QFactorsThroughHomotopy_of_exists_prev [CategoryWithHomology C] :
    c.QFactorsThroughHomotopy C where
  areEqualizedByLocalization {K L f g} h := by
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc _
      (MorphismProperty.IsInvertedBy.of_le _ _ _
        (Localization.inverts _ (HomologicalComplex.quasiIso C _))
        (homotopyEquivalences_le_quasiIso C _))
end Cylinder
section ChainComplex
variable (C : Type*) [Category C] {ι : Type*} [Preadditive C]
  [AddRightCancelSemigroup ι] [One ι] [HasBinaryBiproducts C]
instance : (HomotopyCategory.quotient C (ComplexShape.down ι)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.down ι).quotient_isLocalization (fun _ => ⟨_, rfl⟩) C
variable [CategoryWithHomology C]
instance : (ComplexShape.down ι).QFactorsThroughHomotopy C :=
  (ComplexShape.down ι).QFactorsThroughHomotopy_of_exists_prev (fun _ => ⟨_, rfl⟩) C
example [(HomologicalComplex.quasiIso C (ComplexShape.down ι)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
    (HomotopyCategory.quasiIso C (ComplexShape.down ι)) :=
  inferInstance
end ChainComplex
section CochainComplex
variable (C : Type*) [Category C] {ι : Type*} [Preadditive C] [HasBinaryBiproducts C]
instance : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.up ℤ).quotient_isLocalization (fun n => ⟨n - 1, by simp⟩) C
variable [CategoryWithHomology C]
instance : (ComplexShape.up ℤ).QFactorsThroughHomotopy C :=
  (ComplexShape.up ℤ).QFactorsThroughHomotopy_of_exists_prev (fun n => ⟨n - 1, by simp⟩) C
example [(HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  inferInstance
end CochainComplex
namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {ι : Type*} (c : ComplexShape ι)
section
variable [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  [(HomologicalComplex.quasiIso D c).HasLocalization]
  [F.Additive] [F.PreservesHomology]
@[simps]
def mapHomologicalComplexUpToQuasiIsoLocalizerMorphism :
    LocalizerMorphism (HomologicalComplex.quasiIso C c) (HomologicalComplex.quasiIso D c) where
  functor := F.mapHomologicalComplex c
  map _ _ f (_ : QuasiIso f) := HomologicalComplex.quasiIso_map_of_preservesHomology _ _
lemma mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso :
    (HomologicalComplex.quasiIso C c).IsInvertedBy
      (F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q) := by
  apply (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).inverts
variable [(HomologicalComplex.quasiIso C c).HasLocalization]
noncomputable def mapHomologicalComplexUpToQuasiIso :
    HomologicalComplexUpToQuasiIso C c ⥤ HomologicalComplexUpToQuasiIso D c :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).localizedFunctor
    HomologicalComplexUpToQuasiIso.Q HomologicalComplexUpToQuasiIso.Q
noncomputable instance :
    Localization.Lifting HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c)
      (F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q)
      (F.mapHomologicalComplexUpToQuasiIso c) :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).liftingLocalizedFunctor _ _
noncomputable def mapHomologicalComplexUpToQuasiIsoFactors :
    HomologicalComplexUpToQuasiIso.Q ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅
      F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q :=
  Localization.Lifting.iso HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c) _ _
variable [c.QFactorsThroughHomotopy C] [c.QFactorsThroughHomotopy D]
  [(HomotopyCategory.quotient C c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C c)]
noncomputable def mapHomologicalComplexUpToQuasiIsoFactorsh :
    HomologicalComplexUpToQuasiIso.Qh ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅
      F.mapHomotopyCategory c ⋙ HomologicalComplexUpToQuasiIso.Qh :=
  Localization.liftNatIso (HomotopyCategory.quotient C c)
    (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quotient C c ⋙ HomologicalComplexUpToQuasiIso.Qh ⋙
      F.mapHomologicalComplexUpToQuasiIso c)
    (HomotopyCategory.quotient C c ⋙ F.mapHomotopyCategory c ⋙
      HomologicalComplexUpToQuasiIso.Qh) _ _
      (F.mapHomologicalComplexUpToQuasiIsoFactors c)
noncomputable instance :
    Localization.Lifting HomologicalComplexUpToQuasiIso.Qh (HomotopyCategory.quasiIso C c)
      (F.mapHomotopyCategory c ⋙ HomologicalComplexUpToQuasiIso.Qh)
      (F.mapHomologicalComplexUpToQuasiIso c) :=
  ⟨F.mapHomologicalComplexUpToQuasiIsoFactorsh c⟩
variable {c}
@[reassoc]
lemma mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexUpToQuasiIsoFactorsh c).hom.app
        ((HomotopyCategory.quotient _ _).obj K) =
      (F.mapHomologicalComplexUpToQuasiIso c).map
          ((HomologicalComplexUpToQuasiIso.quotientCompQhIso C c).hom.app K) ≫
        (F.mapHomologicalComplexUpToQuasiIsoFactors c).hom.app K ≫
          (HomologicalComplexUpToQuasiIso.quotientCompQhIso D c).inv.app _ ≫
            HomologicalComplexUpToQuasiIso.Qh.map
              ((F.mapHomotopyCategoryFactors c).inv.app K) := by
  dsimp [mapHomologicalComplexUpToQuasiIsoFactorsh]
  rw [Localization.liftNatTrans_app]
  dsimp
  simp only [Category.comp_id, Category.id_comp]
  change _ = (F.mapHomologicalComplexUpToQuasiIso c).map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    HomologicalComplexUpToQuasiIso.Qh.map (𝟙 _)
  simp only [map_id, Category.comp_id, Category.id_comp]
end
end CategoryTheory.Functor