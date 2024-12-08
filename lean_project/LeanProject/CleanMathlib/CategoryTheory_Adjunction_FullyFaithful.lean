import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.EpiMono
open CategoryTheory
namespace CategoryTheory.Adjunction
universe v₁ v₂ u₁ u₂
open Category
open Opposite
attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
attribute [local simp] homEquiv_unit homEquiv_counit
instance unit_mono_of_L_faithful [L.Faithful] (X : C) : Mono (h.unit.app X) where
  right_cancellation {Y} f g hfg :=
    L.map_injective <| (h.homEquiv Y (L.obj X)).injective <| by simpa using hfg
noncomputable def unitSplitEpiOfLFull [L.Full] (X : C) : SplitEpi (h.unit.app X) where
  section_ := L.preimage (h.counit.app (L.obj X))
  id := by simp [← h.unit_naturality (L.preimage (h.counit.app (L.obj X)))]
instance unit_isSplitEpi_of_L_full [L.Full] (X : C) : IsSplitEpi (h.unit.app X) :=
  ⟨⟨h.unitSplitEpiOfLFull X⟩⟩
instance [L.Full] [L.Faithful] (X : C) : IsIso (h.unit.app X) :=
  isIso_of_mono_of_isSplitEpi _
instance unit_isIso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso (Adjunction.unit h) :=
  NatIso.isIso_of_isIso_app _
instance counit_epi_of_R_faithful [R.Faithful] (X : D) : Epi (h.counit.app X) where
  left_cancellation {Y} f g hfg :=
    R.map_injective <| (h.homEquiv (R.obj X) Y).symm.injective <| by simpa using hfg
noncomputable def counitSplitMonoOfRFull [R.Full] (X : D) : SplitMono (h.counit.app X) where
  retraction := R.preimage (h.unit.app (R.obj X))
  id := by simp [← h.counit_naturality (R.preimage (h.unit.app (R.obj X)))]
instance counit_isSplitMono_of_R_full [R.Full] (X : D) : IsSplitMono (h.counit.app X) :=
  ⟨⟨h.counitSplitMonoOfRFull X⟩⟩
instance [R.Full] [R.Faithful] (X : D) : IsIso (h.counit.app X) :=
  isIso_of_epi_of_isSplitMono _
instance counit_isIso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (Adjunction.counit h) :=
  NatIso.isIso_of_isIso_app _
@[simp]
theorem inv_map_unit {X : C} [IsIso (h.unit.app X)] :
    inv (L.map (h.unit.app X)) = h.counit.app (L.obj X) :=
  IsIso.inv_eq_of_hom_inv_id (h.left_triangle_components X)
@[simps!]
noncomputable def whiskerLeftLCounitIsoOfIsIsoUnit [IsIso h.unit] : L ⋙ R ⋙ L ≅ L :=
  (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.unit).symm L ≪≫ Functor.leftUnitor _
@[simp]
theorem inv_counit_map {X : D} [IsIso (h.counit.app X)] :
    inv (R.map (h.counit.app X)) = h.unit.app (R.obj X) :=
  IsIso.inv_eq_of_inv_hom_id (h.right_triangle_components X)
@[simps!]
noncomputable def whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _
lemma faithful_L_of_mono_unit_app [∀ X, Mono (h.unit.app X)] : L.Faithful where
  map_injective {X Y f g} hfg := by
    apply Mono.right_cancellation (f := h.unit.app Y)
    apply (h.homEquiv X (L.obj Y)).symm.injective
    simpa using hfg
lemma full_L_of_isSplitEpi_unit_app [∀ X, IsSplitEpi (h.unit.app X)] : L.Full where
  map_surjective {X Y} f := by
    use ((h.homEquiv X (L.obj Y)) f ≫ section_ (h.unit.app Y))
    suffices L.map (section_ (h.unit.app Y)) = h.counit.app (L.obj Y) by simp [this]
    rw [← comp_id (L.map (section_ (h.unit.app Y)))]
    simp only [Functor.comp_obj, Functor.id_obj, comp_id, ← h.left_triangle_components Y,
      ← assoc, ← Functor.map_comp, IsSplitEpi.id, Functor.map_id, id_comp]
noncomputable def fullyFaithfulLOfIsIsoUnit [IsIso h.unit] : L.FullyFaithful where
  preimage {_ Y} f := h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)
lemma faithful_R_of_epi_counit_app [∀ X, Epi (h.counit.app X)] : R.Faithful where
  map_injective {X Y f g} hfg := by
    apply Epi.left_cancellation (f := h.counit.app X)
    apply (h.homEquiv (R.obj X) Y).injective
    simpa using hfg
lemma full_R_of_isSplitMono_counit_app [∀ X, IsSplitMono (h.counit.app X)] : R.Full where
  map_surjective {X Y} f := by
    use (retraction (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f)
    suffices R.map (retraction (h.counit.app X)) = h.unit.app (R.obj X) by simp [this]
    rw [← id_comp (R.map (retraction (h.counit.app X)))]
    simp only [Functor.id_obj, Functor.comp_obj, id_comp, ← h.right_triangle_components X,
      assoc, ← Functor.map_comp, IsSplitMono.id, Functor.map_id, comp_id]
noncomputable def fullyFaithfulROfIsIsoCounit [IsIso h.counit] : R.FullyFaithful where
  preimage {X Y} f := inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f
instance whiskerLeft_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerLeft L h.counit) := by
  have := h.left_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
instance whiskerRight_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerRight h.counit R) := by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp] at this
  rw [this]
  infer_instance
instance whiskerLeft_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerLeft R h.unit) := by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
instance whiskerRight_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerRight h.unit L) := by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
instance [L.Faithful] [L.Full] {Y : C} : IsIso (h.counit.app (L.obj Y)) :=
  isIso_of_hom_comp_eq_id _ (h.left_triangle_components Y)
instance [L.Faithful] [L.Full] {Y : D} : IsIso (R.map (h.counit.app Y)) :=
  isIso_of_hom_comp_eq_id _ (h.right_triangle_components Y)
lemma isIso_counit_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} :
    IsIso (h.counit.app X) ↔ X ∈ L.essImage := by
  constructor
  · intro
    exact ⟨R.obj X, ⟨asIso (h.counit.app X)⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance
lemma mem_essImage_of_counit_isIso (A : D)
    [IsIso (h.counit.app A)] : A ∈ L.essImage :=
  ⟨R.obj A, ⟨asIso (h.counit.app A)⟩⟩
lemma isIso_counit_app_of_iso [L.Faithful] [L.Full] {X : D} {Y : C} (e : X ≅ L.obj Y) :
    IsIso (h.counit.app X) :=
  (isIso_counit_app_iff_mem_essImage h).mpr ⟨Y, ⟨e.symm⟩⟩
instance [R.Faithful] [R.Full] {Y : D} : IsIso (h.unit.app (R.obj Y)) :=
  isIso_of_comp_hom_eq_id _ (h.right_triangle_components Y)
instance [R.Faithful] [R.Full] {X : C} : IsIso (L.map (h.unit.app X)) :=
  isIso_of_comp_hom_eq_id _ (h.left_triangle_components X)
lemma isIso_unit_app_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} :
    IsIso (h.unit.app Y) ↔ Y ∈ R.essImage := by
  constructor
  · intro
    exact ⟨L.obj Y, ⟨(asIso (h.unit.app Y)).symm⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance
theorem mem_essImage_of_unit_isIso (A : C)
    [IsIso (h.unit.app A)] : A ∈ R.essImage :=
  ⟨L.obj A, ⟨(asIso (h.unit.app A)).symm⟩⟩
@[deprecated (since := "2024-06-19")] alias _root_.CategoryTheory.mem_essImage_of_unit_isIso :=
  mem_essImage_of_unit_isIso
lemma isIso_unit_app_of_iso [R.Faithful] [R.Full] {X : D} {Y : C} (e : Y ≅ R.obj X) :
    IsIso (h.unit.app Y) :=
  (isIso_unit_app_iff_mem_essImage h).mpr ⟨X, ⟨e.symm⟩⟩
instance [R.IsEquivalence] : IsIso h.unit := by
  have := fun Y => isIso_unit_app_of_iso h (R.objObjPreimageIso Y).symm
  apply NatIso.isIso_of_isIso_app
instance [L.IsEquivalence] : IsIso h.counit := by
  have := fun X => isIso_counit_app_of_iso h (L.objObjPreimageIso X).symm
  apply NatIso.isIso_of_isIso_app
lemma isEquivalence_left_of_isEquivalence_right (h : L ⊣ R) [R.IsEquivalence] : L.IsEquivalence :=
  h.toEquivalence.isEquivalence_functor
lemma isEquivalence_right_of_isEquivalence_left (h : L ⊣ R) [L.IsEquivalence] : R.IsEquivalence :=
  h.toEquivalence.isEquivalence_inverse
instance [L.IsEquivalence] : IsIso h.unit := by
  have := h.isEquivalence_right_of_isEquivalence_left
  infer_instance
instance [R.IsEquivalence] : IsIso h.counit := by
  have := h.isEquivalence_left_of_isEquivalence_right
  infer_instance
end CategoryTheory.Adjunction