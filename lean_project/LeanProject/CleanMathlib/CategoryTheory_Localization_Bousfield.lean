import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Localization.Adjunction
namespace CategoryTheory
open Category
namespace Localization
variable {C D : Type*} [Category C] [Category D]
namespace LeftBousfield
section
variable (P : C → Prop)
def W : MorphismProperty C := fun _ _ f =>
  ∀ Z, P Z → Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)
variable {P} in
@[simps! apply]
noncomputable def W.homEquiv {X Y : C} {f : X ⟶ Y} (hf : W P f) (Z : C) (hZ : P Z) :
    (Y ⟶ Z) ≃ (X ⟶ Z) :=
  Equiv.ofBijective _ (hf Z hZ)
lemma W_isoClosure : W (isoClosure P) = W P := by
  ext X Y f
  constructor
  · intro hf Z hZ
    exact hf _ (le_isoClosure _ _ hZ)
  · rintro hf Z ⟨Z', hZ', ⟨e⟩⟩
    constructor
    · intro g₁ g₂ eq
      rw [← cancel_mono e.hom]
      apply (hf _ hZ').1
      simp only [reassoc_of% eq]
    · intro g
      obtain ⟨a, h⟩ := (hf _ hZ').2 (g ≫ e.hom)
      exact ⟨a ≫ e.inv, by simp only [reassoc_of% h, e.hom_inv_id, comp_id]⟩
instance : (W P).IsMultiplicative where
  id_mem X Z _ := by simpa [id_comp] using Function.bijective_id
  comp_mem f g hf hg Z hZ := by
    simpa using Function.Bijective.comp (hf Z hZ) (hg Z hZ)
instance : (W P).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff _ (hg Z hZ)]
    simpa using hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff' (hf Z hZ)]
    simpa using hfg Z hZ
lemma W_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : W P f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_epi f]
  · intro g
    exact ⟨inv f ≫ g, by simp⟩
lemma W_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    W P f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hX).2 (𝟙 X)
    exact ⟨g, hg, (hf _ hY).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · apply W_of_isIso
end
section
variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [F.Full] [F.Faithful]
include adj
lemma W_adj_unit_app (X : D) : W (· ∈ Set.range F.obj) (adj.unit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
    (adj.homEquiv X Y)).bijective using 1
  dsimp [Adjunction.homEquiv]
  aesop
lemma W_iff_isIso_map {X Y : D} (f : X ⟶ Y) :
    W (· ∈ Set.range F.obj) f ↔ IsIso (G.map f) := by
  rw [← (W (· ∈ Set.range F.obj)).postcomp_iff _ _ (W_adj_unit_app adj Y)]
  erw [adj.unit.naturality f]
  rw [(W (· ∈ Set.range F.obj)).precomp_iff _ _ (W_adj_unit_app adj X),
    W_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩]
  constructor
  · intro h
    dsimp at h
    exact isIso_of_fully_faithful F (G.map f)
  · intro
    rw [Functor.comp_map]
    infer_instance
lemma W_eq_inverseImage_isomorphisms :
    W (· ∈ Set.range F.obj) = (MorphismProperty.isomorphisms _).inverseImage G := by
  ext P₁ P₂ f
  rw [W_iff_isIso_map adj]
  rfl
lemma isLocalization : G.IsLocalization (W (· ∈ Set.range F.obj)) := by
  rw [W_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization
end
end LeftBousfield
end Localization
end CategoryTheory