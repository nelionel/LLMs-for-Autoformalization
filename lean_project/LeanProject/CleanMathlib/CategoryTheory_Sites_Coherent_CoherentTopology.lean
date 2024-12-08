import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
namespace CategoryTheory
variable {C : Type*} [Category C] [Precoherent C] {X : C}
theorem coherentTopology.mem_sieves_of_hasEffectiveEpiFamily (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) →
        (S ∈ (coherentTopology C) X) := by
  intro ⟨α, _, Y, π, hπ⟩
  apply (coherentCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
  · exact fun _ _ h ↦ by cases h; exact hπ.2 _
  · exact ⟨_, inferInstance, Y, π, rfl, hπ.1⟩
theorem EffectiveEpiFamily.transitive_of_finite {α : Type} [Finite α] {Y : α → C}
    (π : (a : α) → (Y a ⟶ X)) (h : EffectiveEpiFamily Y π) {β : α → Type} [∀ (a : α), Finite (β a)]
    {Y_n : (a : α) → β a → C} (π_n : (a : α) → (b : β a) → (Y_n a b ⟶ Y a))
    (H : ∀ a, EffectiveEpiFamily (Y_n a) (π_n a)) :
    EffectiveEpiFamily
      (fun (c : Σ a, β a) => Y_n c.fst c.snd) (fun c => π_n c.fst c.snd ≫ π c.fst) := by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) ∈ (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentTopology.isSheaf_yoneda_obj W _ h₂
  apply Coverage.Saturate.transitive X (Sieve.generate (Presieve.ofArrows Y π))
  · apply Coverage.Saturate.of
    use α, inferInstance, Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (coherentTopology C).pullback_stable'
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    obtain ⟨i⟩ := hY
    exact ⟨β i, inferInstance, Y_n i, π_n i, H i, fun b ↦
      ⟨Y_n i b, (𝟙 _), π_n i b ≫ π i, ⟨(⟨i, b⟩ : Σ (i : α), β i)⟩, by simp⟩⟩
instance precoherentEffectiveEpiFamilyCompEffectiveEpis
    {α : Type} [Finite α] {Y Z : α → C} (π : (a : α) → (Y a ⟶ X)) [EffectiveEpiFamily Y π]
    (f : (a : α) → Z a ⟶ Y a) [h : ∀ a, EffectiveEpi (f a)] :
    EffectiveEpiFamily _ fun a ↦ f a ≫ π a := by
  simp_rw [effectiveEpi_iff_effectiveEpiFamily] at h
  exact EffectiveEpiFamily.reindex (e := Equiv.sigmaPUnit α) _ _
    (EffectiveEpiFamily.transitive_of_finite (β := fun _ ↦ Unit) _ inferInstance _ h)
theorem coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (S : Sieve X) :
    (S ∈ (coherentTopology C) X) ↔
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) )  := by
  constructor
  · intro h
    induction h with
    | of Y T hS =>
      obtain ⟨a, h, Y', π, h', _⟩ := hS
      refine ⟨a, h, Y', π, inferInstance, fun a' ↦ ?_⟩
      obtain ⟨rfl, _⟩ := h'
      exact ⟨Y' a', 𝟙 Y' a', π a', Presieve.ofArrows.mk a', by simp⟩
    | top Y =>
      exact ⟨Unit, inferInstance, fun _ => Y, fun _ => (𝟙 Y), inferInstance, by simp⟩
    | transitive Y R S _ _ a b =>
      obtain ⟨α, w, Y₁, π, ⟨h₁,h₂⟩⟩ := a
      choose β _ Y_n π_n H using fun a => b (h₂ a)
      exact ⟨(Σ a, β a), inferInstance, fun ⟨a,b⟩ => Y_n a b, fun ⟨a, b⟩ => (π_n a b) ≫ (π a),
        EffectiveEpiFamily.transitive_of_finite _ h₁ _ (fun a => (H a).1),
        fun c => (H c.fst).2 c.snd⟩
  · exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily S
end CategoryTheory