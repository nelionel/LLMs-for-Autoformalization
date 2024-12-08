import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves
namespace CategoryTheory.regularTopology
open Limits
variable {C : Type*} [Category C] [Preregular C] {X : C}
theorem mem_sieves_of_hasEffectiveEpi (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ S.arrows π) → (S ∈ (regularTopology C) X) := by
  rintro ⟨Y, π, h⟩
  have h_le : Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun _ ↦ π)) ≤ S := by
    rw [Sieve.generate_le_iff (Presieve.ofArrows _ _) S]
    apply Presieve.le_of_factorsThru_sieve (Presieve.ofArrows _ _) S _
    intro W g f
    refine ⟨W, 𝟙 W, ?_⟩
    cases f
    exact ⟨π, ⟨h.2, Category.id_comp π⟩⟩
  apply Coverage.saturate_of_superset (regularCoverage C) h_le
  exact Coverage.Saturate.of X _ ⟨Y, π, rfl, h.1⟩
instance {Y Y' : C} (π : Y ⟶ X) [EffectiveEpi π]
    (π' : Y' ⟶ Y) [EffectiveEpi π'] : EffectiveEpi (π' ≫ π) := by
  rw [effectiveEpi_iff_effectiveEpiFamily, ← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows _ _)) ∈ (regularTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => regularTopology.isSheaf_yoneda_obj W _ h₂
  apply Coverage.Saturate.transitive X (Sieve.generate (Presieve.ofArrows (fun () ↦ Y)
      (fun () ↦ π)))
  · apply Coverage.Saturate.of
    use Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (regularTopology C).pullback_stable'
    apply regularTopology.mem_sieves_of_hasEffectiveEpi
    cases hY
    exact ⟨Y', π', inferInstance, Y', (𝟙 _), π' ≫ π, Presieve.ofArrows.mk (), (by simp)⟩
theorem mem_sieves_iff_hasEffectiveEpi (S : Sieve X) :
    (S ∈ (regularTopology C) X) ↔
    ∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π) := by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      rcases hS with ⟨Y', π, h'⟩
      refine ⟨Y', π, h'.2, ?_⟩
      rcases h' with ⟨rfl, _⟩
      exact ⟨Y', 𝟙 Y', π, Presieve.ofArrows.mk (), (by simp)⟩
    | top Y => exact ⟨Y, (𝟙 Y), inferInstance, by simp only [Sieve.top_apply, forall_const]⟩
    | transitive Y R S _ _ a b =>
      rcases a with ⟨Y₁, π, ⟨h₁,h₂⟩⟩
      choose Y' π' _ H using b h₂
      exact ⟨Y', π' ≫ π, inferInstance, (by simpa using H)⟩
  · exact regularTopology.mem_sieves_of_hasEffectiveEpi S
end CategoryTheory.regularTopology