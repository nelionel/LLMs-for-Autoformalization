import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
universe v u
open CategoryTheory Topology
namespace AlgebraicGeometry
@[mk_iff]
class IsPreimmersion {X Y : Scheme} (f : X ⟶ Y) extends SurjectiveOnStalks f : Prop where
  base_embedding : IsEmbedding f.base
lemma Scheme.Hom.isEmbedding {X Y : Scheme} (f : Hom X Y) [IsPreimmersion f] : IsEmbedding f.base :=
  IsPreimmersion.base_embedding
@[deprecated (since := "2024-10-26")]
alias Scheme.Hom.embedding := Scheme.Hom.isEmbedding
lemma isPreimmersion_eq_inf :
    @IsPreimmersion = (@SurjectiveOnStalks ⊓ topologically IsEmbedding : MorphismProperty _) := by
  ext
  rw [isPreimmersion_iff]
  rfl
instance isSurjectiveOnStalks_isLocalAtTarget : IsLocalAtTarget
    (stalkwise (Function.Surjective ·)) :=
  stalkwiseIsLocalAtTarget_of_respectsIso RingHom.surjective_respectsIso
namespace IsPreimmersion
instance : IsLocalAtTarget @IsPreimmersion :=
  isPreimmersion_eq_inf ▸ inferInstance
instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : IsPreimmersion f where
  base_embedding := f.isOpenEmbedding.isEmbedding
  surj_on_stalks _ := (ConcreteCategory.bijective_of_isIso _).2
instance : MorphismProperty.IsMultiplicative @IsPreimmersion where
  id_mem _ := inferInstance
  comp_mem f g _ _ := ⟨g.isEmbedding.comp f.isEmbedding⟩
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
    [IsPreimmersion g] : IsPreimmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance
instance (priority := 900) {X Y} (f : X ⟶ Y) [IsPreimmersion f] : Mono f := by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact f.isEmbedding.injective
  · exact fun x ↦ ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)
theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
    [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  base_embedding := by
    have h := (f ≫ g).isEmbedding
    rwa [← g.isEmbedding.of_comp_iff]
  surj_on_stalks x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.stalkMap_comp] at h
    exact Function.Surjective.of_comp h
theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] :
    IsPreimmersion (f ≫ g) ↔ IsPreimmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩
lemma Spec_map_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPreimmersion (Spec.map f) ↔ IsEmbedding (PrimeSpectrum.comap f) ∧ f.SurjectiveOnStalks := by
  haveI : (RingHom.toMorphismProperty <| fun f ↦ Function.Surjective f).RespectsIso := by
    rw [← RingHom.toMorphismProperty_respectsIso_iff]
    exact RingHom.surjective_respectsIso
  rw [← HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks), isPreimmersion_iff, and_comm]
  rfl
lemma mk_Spec_map {R S : CommRingCat.{u}} {f : R ⟶ S}
    (h₁ : IsEmbedding (PrimeSpectrum.comap f)) (h₂ : f.SurjectiveOnStalks) :
    IsPreimmersion (Spec.map f) :=
  (Spec_map_iff f).mpr ⟨h₁, h₂⟩
lemma of_isLocalization {R S : Type u} [CommRing R] (M : Submonoid R) [CommRing S]
    [Algebra R S] [IsLocalization M S] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom <| algebraMap R S)) :=
  IsPreimmersion.mk_Spec_map
    (PrimeSpectrum.localization_comap_isEmbedding (R := R) S M)
    (RingHom.surjectiveOnStalks_of_isLocalization (M := M) S)
open Limits MorphismProperty in
instance : IsStableUnderBaseChange @IsPreimmersion := by
  refine .mk' fun X Y Z f g _ _ ↦ ?_
  have := pullback_fst (P := @SurjectiveOnStalks) f g inferInstance
  constructor
  let L (x : (pullback f g : _)) : { x : X × Y | f.base x.1 = g.base x.2 } :=
    ⟨⟨(pullback.fst f g).base x, (pullback.snd f g).base x⟩,
    by simp only [Set.mem_setOf, ← Scheme.comp_base_apply, pullback.condition]⟩
  have : IsEmbedding L := IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
    (SurjectiveOnStalks.isEmbedding_pullback f g)
  exact IsEmbedding.subtypeVal.comp ((TopCat.pullbackHomeoPreimage _ f.continuous _
    g.isEmbedding).isEmbedding.comp this)
end IsPreimmersion
end AlgebraicGeometry