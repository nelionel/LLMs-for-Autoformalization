import Mathlib.Combinatorics.Additive.FreimanHom
open Set
variable {G H : Type*}
section AddCommMonoid
variable [AddCommMonoid G] [AddCommMonoid H] {A B : Set (G × G)} {s : Set G} {t : Set H} {f : G → H}
  {x₁ y₁ x₂ y₂ : G}
@[mk_iff]
structure IsCorner (A : Set (G × G)) (x₁ y₁ x₂ y₂ : G) : Prop where
  fst_fst_mem : (x₁, y₁) ∈ A
  fst_snd_mem : (x₁, y₂) ∈ A
  snd_fst_mem : (x₂, y₁) ∈ A
  add_eq_add : x₁ + y₂ = x₂ + y₁
def IsCornerFree (A : Set (G × G)) : Prop := ∀ ⦃x₁ y₁ x₂ y₂⦄, IsCorner A x₁ y₁ x₂ y₂ → x₁ = x₂
lemma isCornerFree_iff (hAs : A ⊆ s ×ˢ s) :
    IsCornerFree A ↔ ∀ ⦃x₁⦄, x₁ ∈ s → ∀ ⦃y₁⦄, y₁ ∈ s → ∀ ⦃x₂⦄, x₂ ∈ s → ∀ ⦃y₂⦄, y₂ ∈ s →
      IsCorner A x₁ y₁ x₂ y₂ → x₁ = x₂ where
  mp hA _x₁ _ _y₁ _ _x₂ _ _y₂ _ hxy := hA hxy
  mpr hA _x₁ _y₁ _x₂ _y₂ hxy := hA (hAs hxy.fst_fst_mem).1 (hAs hxy.fst_fst_mem).2
    (hAs hxy.snd_fst_mem).1 (hAs hxy.fst_snd_mem).2 hxy
lemma IsCorner.mono (hAB : A ⊆ B) (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner B x₁ y₁ x₂ y₂ where
  fst_fst_mem := hAB hA.fst_fst_mem
  fst_snd_mem := hAB hA.fst_snd_mem
  snd_fst_mem := hAB hA.snd_fst_mem
  add_eq_add := hA.add_eq_add
lemma IsCornerFree.mono (hAB : A ⊆ B) (hB : IsCornerFree B) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxyd ↦ hB <| hxyd.mono hAB
@[simp] lemma not_isCorner_empty : ¬ IsCorner ∅ x₁ y₁ x₂ y₂ := by simp [isCorner_iff]
@[simp] lemma Set.Subsingleton.isCornerFree (hA : A.Subsingleton) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxyd ↦ by simpa using hA hxyd.fst_fst_mem hxyd.snd_fst_mem
lemma isCornerFree_empty : IsCornerFree (∅ : Set (G × G)) := subsingleton_empty.isCornerFree
lemma isCornerFree_singleton (x : G × G) : IsCornerFree {x} := subsingleton_singleton.isCornerFree
lemma IsCorner.image (hf : IsAddFreimanHom 2 s t f) (hAs : (A : Set (G × G)) ⊆ s ×ˢ s)
    (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner (Prod.map f f '' A) (f x₁) (f y₁) (f x₂) (f y₂) := by
  obtain ⟨hx₁y₁, hx₁y₂, hx₂y₁, hxy⟩ := hA
  exact ⟨mem_image_of_mem _ hx₁y₁, mem_image_of_mem _ hx₁y₂, mem_image_of_mem _ hx₂y₁,
    hf.add_eq_add (hAs hx₁y₁).1 (hAs hx₁y₂).2 (hAs hx₂y₁).1 (hAs hx₁y₁).2 hxy⟩
lemma IsCornerFree.of_image (hf : IsAddFreimanHom 2 s t f) (hf' : s.InjOn f)
    (hAs : (A : Set (G × G)) ⊆ s ×ˢ s) (hA : IsCornerFree (Prod.map f f '' A)) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxy ↦
    hf' (hAs hxy.fst_fst_mem).1 (hAs hxy.snd_fst_mem).1 <| hA <| hxy.image hf hAs
lemma isCorner_image (hf : IsAddFreimanIso 2 s t f) (hAs : A ⊆ s ×ˢ s)
    (hx₁ : x₁ ∈ s) (hy₁ : y₁ ∈ s) (hx₂ : x₂ ∈ s) (hy₂ : y₂ ∈ s) :
    IsCorner (Prod.map f f '' A) (f x₁) (f y₁) (f x₂) (f y₂) ↔ IsCorner A x₁ y₁ x₂ y₂ := by
  have hf' := hf.bijOn.injOn.prodMap hf.bijOn.injOn
  rw [isCorner_iff, isCorner_iff]
  congr!
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₁)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₂)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₂ hy₁)
  · exact hf.add_eq_add hx₁ hy₂ hx₂ hy₁
lemma isCornerFree_image (hf : IsAddFreimanIso 2 s t f) (hAs : A ⊆ s ×ˢ s) :
    IsCornerFree (Prod.map f f '' A) ↔ IsCornerFree A := by
  have : Prod.map f f '' A ⊆ t ×ˢ t :=
    ((hf.bijOn.mapsTo.prodMap hf.bijOn.mapsTo).mono hAs Subset.rfl).image_subset
  rw [isCornerFree_iff hAs, isCornerFree_iff this]
  simp +contextual only [hf.bijOn.forall, isCorner_image hf hAs, hf.bijOn.injOn.eq_iff]
alias ⟨IsCorner.of_image, _⟩ := isCorner_image
alias ⟨_, IsCornerFree.image⟩ := isCornerFree_image
end AddCommMonoid