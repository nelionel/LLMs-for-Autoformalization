import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Sites.Sheafification
namespace CategoryTheory
open Localization
variable {C : Type*} [Category C] (J : GrothendieckTopology C) {A : Type*} [Category A]
namespace GrothendieckTopology
abbrev W : MorphismProperty (Cᵒᵖ ⥤ A) := LeftBousfield.W (Presheaf.IsSheaf J)
variable (A) in
lemma W_eq_W_range_sheafToPresheaf_obj :
    J.W = LeftBousfield.W (· ∈ Set.range (sheafToPresheaf J A).obj) := by
  apply congr_arg
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.cond
lemma W_sheafToPreheaf_map_iff_isIso {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂) :
    J.W ((sheafToPresheaf J A).map φ) ↔ IsIso φ := by
  rw [W_eq_W_range_sheafToPresheaf_obj, LeftBousfield.W_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩,
    isIso_iff_of_reflects_iso]
section Adjunction
variable {G : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A}
lemma W_adj_unit_app (adj : G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A) : J.W (adj.unit.app P) := by
  rw [W_eq_W_range_sheafToPresheaf_obj]
  exact LeftBousfield.W_adj_unit_app adj P
lemma W_iff_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A)
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso (G.map f) := by
  rw [W_eq_W_range_sheafToPresheaf_obj]
  exact LeftBousfield.W_iff_isIso_map adj f
lemma W_eq_inverseImage_isomorphisms_of_adjunction (adj : G ⊣ sheafToPresheaf J A) :
    J.W = (MorphismProperty.isomorphisms _).inverseImage G := by
  rw [W_eq_W_range_sheafToPresheaf_obj,
    LeftBousfield.W_eq_inverseImage_isomorphisms adj]
end Adjunction
section HasWeakSheafify
variable [HasWeakSheafify J A]
lemma W_toSheafify (P : Cᵒᵖ ⥤ A) : J.W (toSheafify J P) :=
  J.W_adj_unit_app (sheafificationAdjunction J A) P
lemma W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso ((presheafToSheaf J A).map f) :=
  J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J A) f
variable (A) in
lemma W_eq_inverseImage_isomorphisms :
    J.W = (MorphismProperty.isomorphisms _).inverseImage (presheafToSheaf J A) :=
  J.W_eq_inverseImage_isomorphisms_of_adjunction (sheafificationAdjunction J A)
instance : (presheafToSheaf J A).IsLocalization J.W := by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization
end HasWeakSheafify
end GrothendieckTopology
end CategoryTheory