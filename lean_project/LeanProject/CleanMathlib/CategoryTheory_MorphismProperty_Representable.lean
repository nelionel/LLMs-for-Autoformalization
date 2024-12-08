import Mathlib.CategoryTheory.MorphismProperty.Limits
namespace CategoryTheory
open Category Limits MorphismProperty
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
def Functor.relativelyRepresentable : MorphismProperty D :=
  fun X Y f ↦ ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g
namespace Functor.relativelyRepresentable
section
variable {F}
variable {X Y : D} {f : X ⟶ Y} (hf : F.relativelyRepresentable f)
  {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f')
  {a : C} (g : F.obj a ⟶ Y) (hg : F.relativelyRepresentable g)
noncomputable def pullback : C :=
  (hf g).choose
noncomputable abbrev snd : hf.pullback g ⟶ a :=
  (hf g).choose_spec.choose
noncomputable abbrev fst : F.obj (hf.pullback g) ⟶ X :=
  (hf g).choose_spec.choose_spec.choose
noncomputable abbrev fst' [Full F] : hf'.pullback g ⟶ b :=
  F.preimage (hf'.fst g)
lemma map_fst' [Full F] : F.map (hf'.fst' g) = hf'.fst g :=
  F.map_preimage _
lemma isPullback : IsPullback (hf.fst g) (F.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec
@[reassoc]
lemma w : hf.fst g ≫ f = F.map (hf.snd g) ≫ g := (hf.isPullback g).w
lemma isPullback' [Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g :=
  (hf'.map_fst' _) ▸ hf'.isPullback g
@[reassoc]
lemma w' {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z)
    [Full F] [Faithful F] : hf.fst' (F.map g) ≫ f = hf.snd (F.map g) ≫ g :=
  F.map_injective <| by simp [(hf.w (F.map g))]
lemma isPullback_of_map {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f))
    (g : Y ⟶ Z) [Full F] [Faithful F] :
    IsPullback (hf.fst' (F.map g)) (hf.snd (F.map g)) f g :=
  IsPullback.of_map F (hf.w' g) (hf.isPullback' (F.map g))
variable {g}
@[ext 100]
lemma hom_ext [Faithful F] {c : C} {a b : c ⟶ hf.pullback g}
    (h₁ : F.map a ≫ hf.fst g = F.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  F.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using F.congr_map h₂)
@[ext]
lemma hom_ext' [Full F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g}
    (h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [map_fst'] using F.congr_map h₁) h₂
section
variable {c : C} (i : F.obj c ⟶ X) (h : c ⟶ a) (hi : i ≫ f = F.map h ≫ g)
noncomputable def lift [Full F] : c ⟶ hf.pullback g :=
  F.preimage <| PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi
@[reassoc (attr := simp)]
lemma lift_fst [Full F] : F.map (hf.lift i h hi) ≫ hf.fst g = i := by
  simpa [lift] using PullbackCone.IsLimit.lift_fst _ _ _ _
@[reassoc (attr := simp)]
lemma lift_snd [Full F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h :=
  F.map_injective <| by simpa [lift] using PullbackCone.IsLimit.lift_snd _ _ _ _
end
section
variable {c : C} (i : c ⟶ b) (h : c ⟶ a) (hi : F.map i ≫ f' = F.map h ≫ g)
noncomputable def lift' [Full F] : c ⟶ hf'.pullback g := hf'.lift _ _ hi
@[reassoc (attr := simp)]
lemma lift'_fst [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.fst' g = i :=
  F.map_injective (by simp [map_fst', lift'])
@[reassoc (attr := simp)]
lemma lift'_snd [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']
end
noncomputable def symmetry [Full F] : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm
@[reassoc (attr := simp)]
lemma symmetry_fst [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g := by
  simp [symmetry]
@[reassoc (attr := simp)]
lemma symmetry_snd [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g := by
  simp [symmetry]
@[reassoc (attr := simp)]
lemma symmetry_symmetry [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ :=
  hom_ext' hf' (by simp) (by simp)
@[simps]
noncomputable def symmetryIso [Full F] [Faithful F] : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'
instance [Full F] [Faithful F] : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom
end
lemma map [Full F] [HasPullbacks C] {a b : C} (f : a ⟶ b)
    [∀ c (g : c ⟶ b), PreservesLimit (cospan f g) F] :
    F.relativelyRepresentable (F.map f) := fun c g ↦ by
  obtain ⟨g, rfl⟩ := F.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, F.map (Limits.pullback.fst f g), ?_⟩
  apply F.map_isPullback <| IsPullback.of_hasPullback f g
lemma of_isIso {X Y : D} (f : X ⟶ Y) [IsIso f] : F.relativelyRepresentable f :=
  fun a g ↦ ⟨a, 𝟙 a, g ≫ CategoryTheory.inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩
lemma isomorphisms_le : MorphismProperty.isomorphisms D ≤ F.relativelyRepresentable :=
  fun _ _ f hf ↦ letI : IsIso f := hf; of_isIso F f
instance isMultiplicative : IsMultiplicative F.relativelyRepresentable where
  id_mem _ := of_isIso F _
  comp_mem {F G H} f g hf hg := fun X h ↦
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩
instance isStableUnderBaseChange : IsStableUnderBaseChange F.relativelyRepresentable where
  of_isPullback {X Y Y' X' f g f' g'} P₁ hg a h := by
    refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
    · apply P₁.lift (hg.fst (h ≫ f)) (F.map (hg.snd (h ≫ f)) ≫ h) (by simpa using hg.w (h ≫ f))
    · apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁
instance respectsIso : RespectsIso F.relativelyRepresentable :=
  (isStableUnderBaseChange F).respectsIso
end Functor.relativelyRepresentable
namespace MorphismProperty
open Functor.relativelyRepresentable
variable {X Y : D} (P : MorphismProperty C)
def relative : MorphismProperty D :=
  fun X Y f ↦ F.relativelyRepresentable f ∧
    ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd
abbrev presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v₁) := P.relative yoneda
variable {P} {F}
lemma relative.rep {f : X ⟶ Y} (hf : P.relative F f) : F.relativelyRepresentable f :=
  hf.1
lemma relative.property {f : X ⟶ Y} (hf : P.relative F f) :
    ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
    (_ : IsPullback fst (F.map snd) f g), P snd :=
  hf.2
lemma relative.property_snd {f : X ⟶ Y} (hf : P.relative F f) {a : C} (g : F.obj a ⟶ Y) :
    P (hf.rep.snd g) :=
  hf.property g _ _ (hf.rep.isPullback g)
lemma relative.of_exists [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (h₀ : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd) : P.relative F f := by
  refine ⟨fun a g ↦ ?_, fun a b g fst snd h ↦ ?_⟩
  all_goals obtain ⟨c, g_fst, g_snd, BC, H⟩ := h₀ g
  · refine ⟨c, g_snd, g_fst, BC⟩
  · refine (P.arrow_mk_iso_iff ?_).2 H
    exact Arrow.isoMk (F.preimageIso (h.isoIsPullback X (F.obj a) BC)) (Iso.refl _)
      (F.map_injective (by simp))
lemma relative_of_snd [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (hf : F.relativelyRepresentable f) (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.snd g)) :
    P.relative F f :=
  relative.of_exists (fun _ g ↦ ⟨hf.pullback g, hf.fst g, hf.snd g, hf.isPullback g, h g⟩)
lemma relative_map [F.Faithful] [F.Full] [HasPullbacks C] [IsStableUnderBaseChange P]
    {a b : C} {f : a ⟶ b} [∀ c (g : c ⟶ b), PreservesLimit (cospan f g) F]
    (hf : P f) : P.relative F (F.map f) := by
  apply relative.of_exists
  intro Y' g
  obtain ⟨g, rfl⟩ := F.map_surjective g
  exact ⟨_, _, _, (IsPullback.of_hasPullback f g).map F, P.pullback_snd _ _ hf⟩
lemma of_relative_map {a b : C} {f : a ⟶ b} (hf : P.relative F (F.map f)) : P f :=
  hf.property (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (F.map f))
lemma relative_map_iff [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
    [HasPullbacks C] [IsStableUnderBaseChange P] {X Y : C} {f : X ⟶ Y} :
    P.relative F (F.map f) ↔ P f :=
  ⟨fun hf ↦ of_relative_map hf, fun hf ↦ relative_map hf⟩
lemma relative_monotone {P' : MorphismProperty C} (h : P ≤ P') :
    P.relative F ≤ P'.relative F := fun _ _ _ hf ↦
  ⟨hf.rep, fun _ _ g fst snd BC ↦ h _ (hf.property g fst snd BC)⟩
section
variable (P)
lemma relative_isStableUnderBaseChange : IsStableUnderBaseChange (P.relative F) where
  of_isPullback hfBC hg :=
    ⟨of_isPullback hfBC hg.rep,
      fun _ _ _ _ _ BC ↦ hg.property _ _ _ (IsPullback.paste_horiz BC hfBC)⟩
instance relative_isStableUnderComposition [F.Faithful] [F.Full] [P.IsStableUnderComposition] :
    IsStableUnderComposition (P.relative F) where
  comp_mem {F G H} f g hf hg := by
    refine ⟨comp_mem _ _ _ hf.1 hg.1, fun Z X p fst snd h ↦ ?_⟩
    rw [← hg.1.lift_snd (fst ≫ f) snd (by simpa using h.w)]
    refine comp_mem _ _ _ (hf.property (hg.1.fst p) fst _
      (IsPullback.of_bot ?_ ?_ (hg.1.isPullback p))) (hg.property_snd p)
    · rw [← Functor.map_comp, lift_snd]
      exact h
    · symm
      apply hg.1.lift_fst
instance relative_respectsIso : RespectsIso (P.relative F) :=
  (relative_isStableUnderBaseChange P).respectsIso
instance relative_isMultiplicative [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso] :
    IsMultiplicative (P.relative F) where
  id_mem X := relative.of_exists
    (fun Y g ↦ ⟨Y, g, 𝟙 Y, by simpa using IsPullback.of_id_snd, id_mem _ _⟩)
end
lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_yoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map this =≫ (hf.rep.fst (a ≫ f))
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)), lift_snd]
end MorphismProperty
end CategoryTheory