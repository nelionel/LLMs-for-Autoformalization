import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
namespace CategoryTheory
variable {C : Type*} [Category C] [Precoherent C]
universe w in
lemma isSheaf_coherent (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (coherentTopology C) P ↔
    (∀ (B : C) (α : Type) [Finite α] (X : α → C) (π : (a : α) → (X a ⟶ B)),
      EffectiveEpiFamily X π → (Presieve.ofArrows X π).IsSheafFor P) := by
  constructor
  · intro hP B α _ X π h
    simp only [coherentTopology, Presieve.isSheaf_coverage] at hP
    apply hP
    exact ⟨α, inferInstance, X, π, rfl, h⟩
  · intro h
    simp only [coherentTopology, Presieve.isSheaf_coverage]
    rintro B S ⟨α, _, X, π, rfl, hS⟩
    exact h _ _ _ _ hS
namespace coherentTopology
theorem isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda.obj W) := by
  rw [isSheaf_coherent]
  intro X α _ Y π H
  have h_colim := isColimitOfEffectiveEpiFamilyStruct Y π H.effectiveEpiFamily.some
  rw [← Sieve.generateFamily_eq] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows Y π)
  obtain ⟨t, t_amalg, t_uniq⟩ : ∃! t, x_ext.IsAmalgamation t :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert Presieve.isAmalgamation_restrict (Sieve.le_generate (Presieve.ofArrows Y π)) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy
variable (C) in
instance subcanonical : (coherentTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj
end coherentTopology
end CategoryTheory